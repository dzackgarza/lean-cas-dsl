#!/usr/bin/env python3
"""Durable timing records shared by the existing feedback and acceptance commands."""
from __future__ import annotations

import datetime
from decimal import Decimal
from fractions import Fraction
import fcntl
import hashlib
import json
import os
import platform
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from application_log import dumps_exact_json, loads_application_event


def read_json(path: Path) -> dict:
    return json.loads(path.read_text())


def utc() -> str:
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def digest(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as output:
        temporary = Path(output.name)
        output.write(dumps_exact_json(value))
        output.write("\n")
        output.flush()
        os.fsync(output.fileno())
    os.replace(temporary, path)


def append_record(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a") as output:
        fcntl.flock(output, fcntl.LOCK_EX)
        output.write(dumps_exact_json(value) + "\n")
        output.flush()
        os.fsync(output.fileno())


def identity(context: dict) -> dict:
    return {key: context.get(key) for key in (
        "run", "kind", "revision", "context", "context_status", "parent_run",
        "environment", "workload", "inputs", "log")}


def begin(argv: list[str]) -> None:
    out, kind, reason, log = argv[1:5]
    target_count, stem_count, source_count = map(int, argv[5:8])
    cursor = 8
    targets = argv[cursor:cursor + target_count]
    cursor += target_count
    stems = argv[cursor:cursor + stem_count]
    cursor += stem_count
    sources = argv[cursor:cursor + source_count]
    cursor += source_count
    selection = {"reason": reason, "targets": targets, "acceptance": stems, "sources": sources,
                 "inputs": {source: digest(Path(source)) for source in sources}}
    current = {"kind": kind, "run": Path(out).parent.name, "context": out,
               "log": log, "command": argv[cursor:]}
    if Path(out).exists():
        context = read_json(Path(out))
        if context["context_status"] != "pending" or any(
                context.get(key) != value for key, value in current.items()):
            raise ValueError("a pending feedback selection changed its original run identity")
        context.update(selection)
        atomic_json(Path(out), context)
        return
    context = {
        "utc": utc(), "started_monotonic_ns": time.monotonic_ns(),
        **current, **selection, "context_status": "pending",
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "parent_run": os.environ.get("CAS_FEEDBACK_PARENT_RUN"),
        "environment": {"host": platform.node(), "system": platform.platform(),
                        "machine": platform.machine(), "python": platform.python_version()},
    }
    atomic_json(Path(out), context)
    append_record(Path(out).parent / "events.jsonl",
                  {**identity(context), "event": "run.started", "utc": context["utc"]})


def capture_context(argv: list[str]) -> None:
    import datetime, hashlib, json, os, platform, subprocess, sys
    from pathlib import Path
    out, kind, reason, log = argv[1:5]
    target_count, stem_count, source_count = map(int, argv[5:8])
    cursor = 8
    targets = argv[cursor:cursor + target_count]
    cursor += target_count
    stems = argv[cursor:cursor + stem_count]
    cursor += stem_count
    sources = argv[cursor:cursor + source_count]
    cursor += source_count
    digest = lambda data: hashlib.sha256(data).hexdigest()
    def git_state(path: Path) -> dict[str, str | bool | list[str] | dict[str, str]]:
        def git(*args: str) -> bytes:
            return subprocess.check_output(["git", "-C", str(path), *args])
        revision = git("rev-parse", "HEAD").decode().strip()
        selection = ["--", ".", ":(exclude)timing"]
        diff = git("diff", "--binary", "HEAD", *selection)
        untracked = git("ls-files", "--others", "--exclude-standard", "-z", *selection).decode().split("\0")
        extra = {name: digest((path / name).read_bytes()) for name in untracked if name and (path / name).is_file()}
        return {"path": str(path.resolve()), "revision": revision, "diff_sha256": digest(diff),
                "changed": git("diff", "--name-only", "HEAD", *selection).decode().splitlines(),
                "untracked": extra, "dirty": bool(diff or extra)}
    checkout = Path.cwd()
    manifest_path = checkout / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    resolution = json.loads(subprocess.check_output(
        ["lake", "--log-level=error", "run", "feedback-context"], text=True))
    resolved = resolution["packages"]
    if not resolved or Path(resolved[0]["path"]).resolve() != checkout.resolve():
        raise SystemExit("Lake's resolved workspace does not match this checkout")
    manifest_packages = {package["name"].strip("«»"): package for package in manifest["packages"]}
    dependencies = []
    for package in resolved[1:]:
        name = package["name"]
        path = Path(package["path"]).resolve()
        declared = manifest_packages.get(name)
        declared_path = None
        if declared is not None:
            declared_path = ((checkout / declared["dir"]) if declared["type"] == "path" else
                (checkout / manifest.get("packagesDir", ".lake/packages") / name
                 / (declared.get("subDir") or ""))).resolve()
        configuration = Path(package["configuration"])
        dependencies.append({"name": name, "key": package["key"],
            "manifest_pin": declared.get("rev") if declared else None,
            "manifest_path": str(declared_path) if declared_path else None,
            "matches_manifest_path": path == declared_path,
            "configuration": str(configuration.resolve()),
            "configuration_sha256": digest(configuration.read_bytes()), **git_state(path)})
    inputs = sources.copy()
    from acceptance_inputs import CHECKPOINT, parse_selection
    acceptance_manifest, acceptance = parse_selection(stems)
    if acceptance_manifest is not None:
        inputs.append(acceptance_manifest)
    inputs += [item["source"] for item in acceptance]
    if any(item["kind"] == "extension" for item in acceptance):
        inputs.append(str(CHECKPOINT))
    inputs += ["lean-toolchain", "lake-manifest.json", "lakefile.lean"]
    # Match CasRuntime.installedManifest, including the absent-default observation.
    installed = Path(os.environ.get("CAS_LEAVES", ".lake/packages/cas_leaves"))
    if installed.suffix != ".json":
        installed /= "leaves.json"
    inputs.append(str(installed))
    if "CAS_REALIZATION_PROFILE" in os.environ:
        inputs.append(os.environ["CAS_REALIZATION_PROFILE"])
    input_hashes = {name: digest(Path(name).read_bytes()) if Path(name).is_file() else None for name in inputs}
    source = git_state(checkout)
    environment = {"host": platform.node(), "system": platform.platform(), "machine": platform.machine(),
        "python": platform.python_version(),
        "lean": subprocess.check_output(["lean", "--version"], text=True).strip(),
        "lake": subprocess.check_output(["lake", "--version"], text=True).strip(),
        "selectors": {key: os.environ[key] for key in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SYSROOT",
            "CAS_LEAVES", "CAS_REALIZATION_PROFILE", "CAS_LEAF_CONTRACT_PATH", "CAS_SAGE_PYTHON",
            "CAS_GAP_PYTHON") if key in os.environ}}
    workload = {"targets": targets, "acceptance": stems, "inputs": input_hashes,
                "source": source, "dependencies": dependencies, "resolution": resolution,
                "environment": environment}
    entry = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "kind": kind,
        "run": Path(out).parent.name, "revision": source["revision"], "dirty": source["dirty"],
        "reason": reason, "command": argv[cursor:], "sources": sources, "log": log,
        "workload": digest(json.dumps(workload, sort_keys=True).encode()), **workload}
    prior = read_json(Path(out))
    entry["utc"] = prior["utc"]
    entry["started_monotonic_ns"] = prior["started_monotonic_ns"]
    entry["parent_run"] = prior.get("parent_run")
    entry["context"] = out
    entry["context_status"] = "complete"
    atomic_json(Path(out), entry)
    append_record(Path(out).parent / "events.jsonl",
                  {**identity(entry), "event": "run.context", "context_status": "complete"})

def step_start(argv: list[str]) -> None:
    context_file, phase, source, started, shared = argv[1:6]
    context = read_json(Path(context_file))
    record = {
        **identity(context), "event": "module.started" if phase == "execution" else "phase.started",
        "phase": phase, "step": f"{phase}:{started}", "utc": utc(),
        "started_monotonic_ns": int(started), "source": source or None,
        "module": source.removesuffix(".lean").replace("/", ".") if source else None,
        "input_sha256": digest(Path(source)) if source else None,
        "command": argv[6:], "shared_setup_seconds": int(shared) / 1e9,
        "shared_setup": {"context": context_file, "phases": ["preparation", "build"]},
        "seconds": None, "inclusive_seconds": None, "status": None, "complete": False,
    }
    run = Path(context_file).parent
    atomic_json(run / "steps" / f"{started}.json", record)
    append_record(run / "events.jsonl", record)
    if phase == "execution":
        append_record(Path("timing/modules.jsonl"), record)


def step_finish(argv: list[str]) -> None:
    context_file, started, elapsed, status = argv[1:5]
    path = Path(context_file).parent / "steps" / f"{started}.json"
    record = read_json(path)
    seconds = int(elapsed) / 1e9
    record.update({
        "event": "module.finished" if record["phase"] == "execution" else "phase.finished",
        "finished_utc": utc(), "seconds": seconds, "status": int(status), "complete": True,
        "inclusive_seconds": seconds + record["shared_setup_seconds"],
        "final_input_sha256": digest(Path(record["source"])) if record["source"] else None,
    })
    atomic_json(path, record)
    append_record(path.parent.parent / "events.jsonl", record)
    if record["phase"] == "execution":
        append_record(Path("timing/modules.jsonl"), record)


def collect_computations(context_file: Path, shared_setup_seconds: float) -> dict:
    """Derive records only from the statement runner's durable events, never report rows."""
    context = read_json(context_file)
    run = context_file.parent
    computations: dict[str, dict] = {}
    children: dict[tuple[str, int], dict] = {}
    files: dict[tuple[str, str], dict] = {}
    session_workers: dict[str, str | None] = {}
    beginnings: dict[tuple[str, int], dict] = {}
    malformed: list[str] = []
    invalid_sessions: set[str] = set()
    logs = sorted((run / "application").glob("*.jsonl"))
    for log in logs:
        expected_sequence = 0
        log_session = None
        with log.open() as source:
            for line_number, line in enumerate(source, 1):
                try:
                    event = loads_application_event(line)
                    name, data = event["event"], event["data"]
                    session = event["session"]
                    if not isinstance(name, str) or not isinstance(data, dict):
                        raise ValueError("invalid diagnostic event payload")
                    if not isinstance(session, str) or not session:
                        raise ValueError("invalid diagnostic session")
                    if (type(event["sequence"]) is not int or event["sequence"] < 0
                            or type(event["monotonicMilliseconds"]) is not int
                            or event["monotonicMilliseconds"] < 0
                            or not isinstance(event["parents"], list)
                            or any(type(parent) is not int or not 0 <= parent < event["sequence"]
                                   for parent in event["parents"])):
                        raise ValueError("invalid diagnostic event ancestry or clock")
                    issues = []
                    if event["sequence"] != expected_sequence:
                        issues.append(f"diagnostic sequence {event['sequence']} follows {expected_sequence - 1}")
                    if log_session is None:
                        log_session = session
                        if name != "session.started" or event["sequence"] != 0:
                            issues.append("the diagnostic stream has no original session header")
                    elif session != log_session:
                        issues.append("the diagnostic stream changed its original session")
                        invalid_sessions.add(log_session)
                    if name == "session.started" and event["sequence"] != 0:
                        issues.append("the diagnostic stream repeated its session header")
                    if issues:
                        invalid_sessions.add(session)
                        malformed.extend(f"{log}:{line_number}: {issue}" for issue in issues)
                    # Keep subsequent actual events after a gap; incompleteness must not erase
                    # the terminal outcomes, elapsed work or source evidence that did survive.
                    expected_sequence = event["sequence"] + 1
                    if name == "session.started":
                        worker = data.get("feedbackWorker")
                        if worker is not None and (not isinstance(worker, str) or not worker):
                            raise ValueError("invalid declared feedback worker")
                        session_workers[session] = worker
                    elif name == "file.begin":
                        if not isinstance(data["file"], str) or not data["file"]:
                            raise ValueError("invalid original file name")
                        beginnings[(session, event["sequence"])] = event
                    elif name in {"computation.started", "computation.timing"}:
                        key = data["computation"]
                        for field in ("computation", "fileRun", "file", "sourceSha256"):
                            if not isinstance(data[field], str) or not data[field]:
                                raise ValueError(f"invalid computation {field}")
                        if type(data["ordinal"]) is not int or data["ordinal"] < 0:
                            raise ValueError("invalid computation ordinal")
                        timing_fields = ("cumulativeSetupMilliseconds",) if name == "computation.started" else (
                            "milliseconds", "executionMilliseconds", "setupMilliseconds",
                            "cumulativeSetupMilliseconds")
                        for field in timing_fields:
                            if type(data[field]) not in (int, float, Decimal) or data[field] < 0:
                                raise ValueError(f"invalid computation {field}")
                        if name == "computation.timing":
                            if (data["setupMilliseconds"] != data["cumulativeSetupMilliseconds"]
                                    or Fraction(data["milliseconds"]) !=
                                    Fraction(data["executionMilliseconds"]) + Fraction(data["setupMilliseconds"])):
                                raise ValueError("statement timing lost its inclusive setup")
                            result = data["result"]
                            if (not isinstance(result, dict) or type(result["published"]) is not bool
                                    or type(result["fails"]) is not bool
                                    or not isinstance(result["kind"], str)):
                                raise ValueError("statement timing lost its actual enclosing result")
                        item = computations.setdefault(key, {"source_log": str(log), "session": session})
                        field = "start" if name == "computation.started" else "completion"
                        if field in item or item["session"] != session:
                            raise ValueError(f"duplicate or changed {name} for {key}")
                        item[field] = event
                    elif name in {"statement.child.started", "statement.child.finished",
                                  "statement.child.interrupted"}:
                        if name == "statement.child.started":
                            if (type(data["ordinal"]) is not int or data["ordinal"] < 0
                                    or not isinstance(data["id"], str) or not data["id"]
                                    or not isinstance(data["source"], str)
                                    or not isinstance(data["position"], dict)
                                    or type(data["precedingSetupMilliseconds"]) is not int
                                    or data["precedingSetupMilliseconds"] < 0):
                                raise ValueError("invalid original nested statement or setup")
                            child_sequence = event["sequence"]
                            field = "start"
                        else:
                            if not event["parents"]:
                                raise ValueError("nested terminal event lost its owning start")
                            child_sequence = event["parents"][-1]
                            if type(data["milliseconds"]) not in (int, float, Decimal) or data["milliseconds"] < 0:
                                raise ValueError("invalid nested execution time")
                            field = "completion" if name == "statement.child.finished" else "interruption"
                            if field == "completion" and (
                                    not isinstance(data["kind"], str)
                                    or type(data["attempted"]) is not bool
                                    or type(data["staged"]) is not bool
                                    or data["publication"] != "pending enclosing cell"):
                                raise ValueError("nested result lost its staged publication boundary")
                        item = children.setdefault((session, child_sequence),
                                                   {"source_log": str(log), "session": session})
                        if field in item or (field != "start" and
                                             ("completion" in item or "interruption" in item)):
                            raise ValueError(f"duplicate nested {field} at {session}/{child_sequence}")
                        item[field] = event
                    elif name in {"file.started", "file.finished", "file.failed"}:
                        fields = ("fileRun", "file") if name == "file.failed" else (
                            "fileRun", "file", "sourceSha256")
                        for field in fields:
                            if not isinstance(data[field], str) or not data[field]:
                                raise ValueError(f"invalid file {field}")
                        if name != "file.failed":
                            count_field = "statements" if name == "file.started" else "executed"
                            if type(data[count_field]) is not int or data[count_field] < 0:
                                raise ValueError(f"invalid file {count_field}")
                        elif data["stage"] not in {"read", "parse"} or not isinstance(data["detail"], str):
                            raise ValueError("invalid file failure boundary")
                        item = files.setdefault((session, data["fileRun"]), {})
                        field = {"file.started": "start", "file.finished": "completion",
                                 "file.failed": "failure"}[name]
                        if field in item:
                            raise ValueError(f"duplicate {name} for {data['file']}")
                        item[field] = event
                except (json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
                    malformed.append(f"{log}:{line_number}: {error}")
                    if log_session is not None:
                        invalid_sessions.add(log_session)
    worker_starts = {}
    invalid_workers = set()
    for path in (run / "steps").glob("*.json"):
        try:
            step = read_json(path)
            if not isinstance(step["phase"], str):
                raise ValueError("invalid recorded phase")
            if step["phase"].startswith("acceptance-worker"):
                worker = step["phase"].removeprefix("acceptance-worker")
                if not worker:
                    raise ValueError("an acceptance-worker start lost its declared identity")
                if worker in worker_starts:
                    invalid_workers.add(worker)
                    raise ValueError(f"duplicate original worker start for {worker}")
                started = step["started_monotonic_ns"]
                if type(started) is not int or started < 0:
                    invalid_workers.add(worker)
                    raise ValueError(f"invalid original worker start for {worker}")
                # Compare at the native log's millisecond precision, without clamping
                # a genuinely negative interval or inventing an absent start.
                worker_starts[worker] = started // 1_000_000
        except (json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
            malformed.append(f"{path}: {error}")
    first_files = {}
    for (session, _), event in beginnings.items():
        worker = session_workers.get(session)
        if worker is not None:
            entered = event["monotonicMilliseconds"]
            first_files[worker] = min(first_files.get(worker, entered), entered)
    worker_setup = {}
    for worker, entered in first_files.items():
        started = worker_starts.get(worker)
        if started is None or worker in invalid_workers:
            malformed.append(f"worker {worker} has no unique recorded startup boundary")
            invalid_workers.add(worker)
        elif entered < started:
            malformed.append(f"worker {worker} entered a file before its recorded start")
            invalid_workers.add(worker)
        else:
            worker_setup[worker] = (entered - started) / 1000
    invalid_sessions.update(session for session, worker in session_workers.items()
                            if worker in invalid_workers)
    rows = []
    root_starts = {}
    for key, item in computations.items():
        start, completion = item.get("start"), item.get("completion")
        data = (completion or start)["data"]
        seconds = float(data["milliseconds"] / 1000) if completion else None
        agreed = start is not None and completion is not None
        if agreed:
            agreed = all(start["data"][field] == data[field] for field in
                         ("computation", "fileRun", "file", "ordinal", "sourceSha256",
                          "cumulativeSetupMilliseconds"))
            agreed = agreed and completion["monotonicMilliseconds"] >= start["monotonicMilliseconds"]
        if start and completion and not agreed:
            malformed.append(f"computation {key} changed its original statement, input, or setup")
        worker = session_workers.get(item["session"])
        shared_worker = worker_setup.get(worker) if worker is not None else 0
        row = {
            **identity(context), **item, "unit": "statement", "computation": key,
            "parent_computation": None, "root_computation": key,
            "file": data["file"], "file_run": data["fileRun"], "worker": worker,
            "ordinal": data["ordinal"], "id": data.get("id"),
            "input_sha256": data["sourceSha256"], "seconds": seconds,
            "execution_seconds": float(data["executionMilliseconds"] / 1000) if completion else None,
            "setup_seconds": float(data["cumulativeSetupMilliseconds"] / 1000),
            "shared_setup_seconds": shared_setup_seconds,
            "shared_worker_setup_seconds": shared_worker,
            "shared_setup": {"context": str(context_file), "phases": ["preparation", "build"]},
            "inclusive_seconds": (seconds + shared_setup_seconds + shared_worker
                                  if seconds is not None and shared_worker is not None else None),
            "complete": agreed and shared_worker is not None and item["session"] not in invalid_sessions,
        }
        rows.append(row)
        if start:
            root_starts[(item["session"], start["sequence"])] = row

    # A child's own scope is the final parent of its terminal event. Its ancestors
    # identify the actual file computation and containing child; source text is never a key.
    nested_parents = {}
    nested_roots = {}
    first_children = {}
    for child_key, item in children.items():
        start = item.get("start")
        if start is None:
            malformed.append(f"nested terminal event {child_key} has no original start")
            continue
        ancestors = [(item["session"], sequence) for sequence in reversed(start["parents"])]
        root_key = next((key for key in ancestors if key in root_starts), None)
        if root_key is None:
            continue  # Ordinary Session runs remain fully retained in the raw application log.
        parent_key = next((key for key in ancestors if key in children or key in root_starts), None)
        if parent_key is None:
            malformed.append(f"nested computation {child_key} lost its actual parent")
            continue
        nested_roots[child_key] = root_key
        nested_parents[child_key] = parent_key
        first_children[parent_key] = min(first_children.get(parent_key, start["monotonicMilliseconds"]),
                                         start["monotonicMilliseconds"])

    scoped_rows = dict(root_starts)
    for child_key in sorted(nested_parents):
        item = children[child_key]
        start, completion = item["start"], item.get("completion")
        terminal = completion or item.get("interruption")
        parent_key = nested_parents[child_key]
        parent = scoped_rows.get(parent_key)
        root = root_starts[nested_roots[child_key]]
        setup = None
        preflight = None
        preceding = float(start["data"]["precedingSetupMilliseconds"] / 1000)
        if parent is not None:
            preflight = (first_children[parent_key] - parent["start"]["monotonicMilliseconds"]) / 1000
            if preflight < 0:
                malformed.append(f"nested computation {child_key} precedes its parent")
            elif parent["setup_seconds"] is not None:
                setup = parent["setup_seconds"] + preflight + preceding
        else:
            malformed.append(f"nested computation {child_key} has no recorded containing scope")
        terminal_ordered = terminal is None or terminal["monotonicMilliseconds"] >= start["monotonicMilliseconds"]
        if not terminal_ordered:
            malformed.append(f"nested computation {child_key} has a terminal event before its start")
        execution = float(terminal["data"]["milliseconds"] / 1000) if terminal else None
        seconds = execution + setup if execution is not None and setup is not None else None
        enclosing = root.get("completion", {}).get("data", {}).get("result")
        key = f"{item['session']}/child/{start['sequence']}"
        row = {
            **identity(context), **item, "unit": "nested_statement", "computation": key,
            "parent_computation": parent["computation"] if parent else None,
            "root_computation": root["computation"],
            "file": root["file"], "file_run": root["file_run"], "worker": root["worker"],
            "ordinal": start["data"]["ordinal"], "id": start["data"]["id"],
            "input_sha256": root["input_sha256"], "seconds": seconds,
            "execution_seconds": execution, "setup_seconds": setup,
            "enclosing_preflight_seconds": preflight, "preceding_setup_seconds": preceding,
            "shared_setup_seconds": shared_setup_seconds,
            "shared_worker_setup_seconds": root["shared_worker_setup_seconds"],
            "shared_setup": root["shared_setup"],
            "inclusive_seconds": (seconds + shared_setup_seconds + root["shared_worker_setup_seconds"]
                                  if seconds is not None and root["shared_worker_setup_seconds"] is not None else None),
            "outcome": completion["data"] if completion else None,
            "enclosing_outcome": enclosing,
            "enclosing_published": enclosing["published"] if enclosing is not None else None,
            "complete": (completion is not None and root["complete"] and setup is not None
                         and terminal_ordered),
        }
        rows.append(row)
        scoped_rows[child_key] = row

    complete = not malformed and all(row["complete"] and
        (row["session"], row["file_run"]) in files for row in rows)
    file_records = []
    recorded_beginnings = set()
    for (session, file_run), events in files.items():
        file_rows = [row for row in rows if row["session"] == session and row["file_run"] == file_run]
        starts = [row for row in file_rows if row["unit"] == "statement"]
        nested = [row for row in file_rows if row["unit"] == "nested_statement"]
        start, finish, failure = events.get("start"), events.get("completion"), events.get("failure")
        first = start or finish or failure
        file = first["data"]["file"]
        begin_key = (session, first["parents"][0]) if first["parents"] else None
        begin = beginnings.get(begin_key)
        if begin is not None:
            recorded_beginnings.add(begin_key)
        count = start["data"]["statements"] if start else None
        executed = finish["data"]["executed"] if finish else None
        matched = (failure is None and begin is not None and begin["data"]["file"] == file and
                   count is not None and count == executed == len(starts)
                   and all(row["complete"] for row in file_rows)
                   and len({row["ordinal"] for row in starts}) == len(starts))
        failure_seconds = None
        if failure is not None:
            # A classified read/parse failure is a finished attempt, including in a
            # passing negative-control module. No statement was entered or invented.
            executed = 0
            matched = (begin is not None and begin["data"]["file"] == file and
                       start is None and finish is None and not file_rows)
            if begin is not None:
                failure_seconds = (failure["monotonicMilliseconds"] -
                                   begin["monotonicMilliseconds"]) / 1000
                matched = matched and failure_seconds >= 0
        if start:
            matched = matched and all(
                row["input_sha256"] == start["data"]["sourceSha256"] for row in file_rows)
            if file in context["inputs"]:
                matched = matched and context["inputs"][file] == start["data"]["sourceSha256"]
        if start and finish:
            matched = matched and all(start["data"][field] == finish["data"][field]
                                      for field in ("file", "fileRun", "sourceSha256"))
        matched = matched and session not in invalid_sessions
        complete = complete and matched
        file_records.append({"file": file, "file_run": file_run, "session": session, "statements": count,
                             "executed": executed, "records": len(starts), "nested_records": len(nested),
                             "total_records": len(file_rows), "complete": matched,
                             "begin": begin, "failure": failure, "failure_seconds": failure_seconds})
    for key, begin in beginnings.items():
        if key not in recorded_beginnings:
            complete = False
            file_records.append({"file": begin["data"]["file"], "file_run": None,
                                 "session": key[0], "statements": None, "executed": None,
                                 "records": 0, "nested_records": 0, "total_records": 0,
                                 "complete": False, "begin": begin, "failure": None})
    # The append-only application logs already preserve started work during SIGKILL. These
    # derived records are published once by the owning run's exit handler.
    with (run / "computations.jsonl").open("w") as output:
        for row in rows:
            output.write(dumps_exact_json(row) + "\n")
            append_record(Path("timing/computations.jsonl"), row)
        output.flush()
        os.fsync(output.fileno())
    result = {"complete": complete, "records": len(rows),
              "top_level_records": sum(row["unit"] == "statement" for row in rows),
              "nested_records": sum(row["unit"] == "nested_statement" for row in rows),
              "files": file_records, "malformed": malformed, "logs": [str(log) for log in logs],
              "record_file": str(run / "computations.jsonl")}
    atomic_json(run / "computation-summary.json", result)
    return result


def finish_feedback(argv: list[str]) -> int:
    (records, context_file, status, limit, total, preparation, build, execution, acceptance,
     bs, es, acs, attempted) = argv[1:14]
    attempted_sources = argv[14:]
    context_path = Path(context_file)
    entry = read_json(context_path)
    seconds = int(total) / 1e9
    over = entry["kind"] == "loop" and seconds > int(limit)
    execution_result = int(status)
    result = execution_result or (1 if over else 0)
    shared = (int(preparation) + int(build)) / 1e9
    interrupted = False
    for path in (context_path.parent / "steps").glob("*.json"):
        step = read_json(path)
        if not step["complete"]:
            interrupted = True
            elapsed = (time.monotonic_ns() - step["started_monotonic_ns"]) / 1e9
            step.update({"event": "module.interrupted" if step["phase"] == "execution"
                         else "phase.interrupted", "seconds": elapsed,
                         "inclusive_seconds": elapsed + step["shared_setup_seconds"],
                         "status": execution_result or 1, "finished_utc": utc()})
            atomic_json(path, step)
            append_record(context_path.parent / "events.jsonl", step)
            if step["phase"] == "execution":
                append_record(Path("timing/modules.jsonl"), step)
    for source in entry["sources"]:
        if source not in attempted_sources:
            append_record(Path("timing/modules.jsonl"), {
                **identity(entry), "event": "module.not_run", "source": source,
                "module": source.removesuffix(".lean").replace("/", "."),
                "input_sha256": entry["inputs"].get(source), "seconds": None,
                "inclusive_seconds": None, "shared_setup_seconds": shared,
                "complete": False, "status": None, "run_status": execution_result,
            })
    computations = collect_computations(context_path, shared)
    if not computations["complete"]:
        result = result or 1
    entry.update({
        "seconds": seconds, "status": result, "execution_status": execution_result,
        "over_limit": over, "within_loop_bound": seconds <= int(limit),
        "attempted": attempted == "true", "attempted_sources": attempted_sources,
        "finished_utc": utc(), "complete": not interrupted, "computations": computations,
        "preparation_seconds": int(preparation) / 1e9,
        "phases": {
            **{name: {"seconds": int(elapsed) / 1e9, "status": int(code) if code else None}
               for name, elapsed, code in (("build", build, bs), ("execution", execution, es),
                                          ("acceptance", acceptance, acs))},
        },
    })
    summary = (f"{entry['kind']}: execution status {execution_result}; status {result} "
               f"in {seconds:.3f} s; log {entry['log']}")
    if over:
        summary += (f"\nOVER THE LIMIT: the {limit}-second development loop needs repair. "
                    "The run was allowed to finish.")
    with Path(entry["log"]).open("a") as output:
        output.write(summary + "\n")
    atomic_json(context_path.parent / "result.json", entry)
    append_record(Path(records), entry)
    append_record(context_path.parent / "events.jsonl",
                  {**identity(entry), "event": "run.finished", "status": result,
                   "seconds": seconds, "finished_utc": entry["finished_utc"]})
    print(summary)
    return result


if __name__ == "__main__":
    command = sys.argv[1]
    arguments = [sys.argv[0], *sys.argv[2:]]
    if command == "begin":
        begin(arguments)
    elif command == "context":
        capture_context(arguments)
    elif command == "step-start":
        step_start(arguments)
    elif command == "step-finish":
        step_finish(arguments)
    elif command == "finish":
        raise SystemExit(finish_feedback(arguments))
    else:
        raise SystemExit(f"unknown timing operation: {command}")
