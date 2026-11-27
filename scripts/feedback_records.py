#!/usr/bin/env python3
"""Durable timing records shared by the existing feedback and acceptance commands."""
from __future__ import annotations

import datetime
from decimal import Decimal
from fractions import Fraction
import fcntl
import gzip
import hashlib
import json
import math
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from application_log import dumps_exact_json, loads_application_event
from source_occurrences import reconcile


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


def utc_at(context: dict, monotonic_ns: int) -> str:
    start = datetime.datetime.fromisoformat(context["utc"])
    elapsed = datetime.timedelta(microseconds=(monotonic_ns - context["started_monotonic_ns"]) // 1000)
    return (start + elapsed).isoformat()


def terminal_row(context: dict, *, target: str, input_sha256: str | None,
                 utc_start: str, seconds: float, status: str,
                 log_path: str, log_sha256: str) -> dict:
    if status not in {"pass", "fail", "interrupted"}:
        raise ValueError("invalid terminal timing status")
    if not math.isfinite(seconds) or seconds < 0:
        raise ValueError("invalid terminal timing duration")
    environment = context["environment"]
    return {
        "run_id": context["run"], "parent_run": context.get("parent_run"),
        "utc_start": utc_start, "seconds": seconds, "status": status,
        "revision": context["revision"], "dirty": context["dirty"],
        "environment": {"lean": environment.get("lean"),
                        "image_digest": environment.get("image_digest")},
        "target": target, "input_sha256": input_sha256,
        "log_path": log_path, "log_sha256": log_sha256,
    }


def compress_log(path: Path) -> tuple[str, str]:
    compressed = path if path.suffix == ".gz" else path.with_name(path.name + ".gz")
    if path != compressed and path.is_file():
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode="w+b", dir=path.parent, delete=False) as output:
                temporary = Path(output.name)
                with path.open("rb") as source, gzip.GzipFile(
                        filename="", mode="wb", fileobj=output, mtime=0) as archive:
                    shutil.copyfileobj(source, archive)
                output.flush()
                os.fsync(output.fileno())
            os.replace(temporary, compressed)
            path.unlink()
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)
    if not compressed.is_file():
        raise FileNotFoundError(f"no finalized run log: {compressed}")
    return str(compressed), hashlib.sha256(compressed.read_bytes()).hexdigest()


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
    from acceptance_inputs import parse_selection
    try:
        _, acceptance_files = parse_selection(stems)
    except (OSError, KeyError, TypeError, ValueError, SystemExit):
        acceptance_files = []
    selected_inputs = [*sources, *(item["source"] for item in acceptance_files)]
    selection = {"reason": reason, "targets": targets, "acceptance": stems, "sources": sources,
                 "acceptance_files": acceptance_files,
                 "inputs": {source: digest(Path(source)) for source in selected_inputs}}
    current = {"kind": kind, "run": Path(out).parent.name, "context": out,
               "log": log, "command": argv[cursor:]}
    if Path(out).exists():
        context = read_json(Path(out))
        if context["context_status"] != "pending" or any(
                context.get(key) != value for key, value in current.items()):
            raise ValueError("a pending feedback selection changed its original run identity")
        selection["inputs"] = {**selection["inputs"], **context["inputs"]}
        context.update(selection)
        atomic_json(Path(out), context)
    else:
        context = {
            "utc": utc(), "started_monotonic_ns": time.monotonic_ns(),
            **current, **selection, "context_status": "pending",
            "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
            "dirty": bool(subprocess.check_output([
                "git", "status", "--porcelain", "--untracked-files=all", "--", ".", ":(exclude)timing"])),
            "parent_run": os.environ.get("CAS_FEEDBACK_PARENT_RUN") or None,
            "environment": {"host": platform.node(), "system": platform.platform(),
                            "machine": platform.machine(), "python": platform.python_version(),
                            "lean": None, "image_digest": os.environ.get("CAS_FEEDBACK_IMAGE_DIGEST")},
        }
        atomic_json(Path(out), context)
        append_record(Path(out).parent / "events.jsonl",
                      {**identity(context), "event": "run.started", "utc": context["utc"]})
    if kind == "accept":
        parent = os.environ.get("CAS_FEEDBACK_PARENT_CONTEXT")
        if parent:
            parent_context = read_json(Path(parent))
            if parent_context["run"] != context["parent_run"]:
                raise ValueError("acceptance child changed its original parent run")
            atomic_json(Path(parent).parent / "acceptance-child.json",
                        {"context": out, "run": context["run"]})
        atomic_json(Path(".tmp/accept-current.json"),
                    {"result": str(Path(out).parent / "result.json")})


def capture_identity(context_file: Path) -> None:
    context = read_json(context_file)
    environment = context["environment"]
    environment.update(host=platform.node(), system=platform.platform(), machine=platform.machine(),
                       python=platform.python_version(),
                       image_digest=os.environ.get("CAS_FEEDBACK_IMAGE_DIGEST"))
    try:
        environment["lean"] = subprocess.check_output(["lean", "--version"], text=True).strip()
    finally:
        atomic_json(context_file, context)
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", environment.get("image_digest") or ""):
        raise SystemExit("the running container has no verified image digest")


def capture_context(argv: list[str]) -> None:
    import datetime, hashlib, json, os, platform, subprocess, sys
    from pathlib import Path
    out, kind, reason, log = argv[1:5]
    preparation_started = time.monotonic_ns()
    spans = []

    def measure(phase, action, **details):
        started = time.monotonic_ns()
        value = action()
        spans.append({"phase": phase, **details, "started_monotonic_ns": started,
                      "finished_monotonic_ns": time.monotonic_ns()})
        return value

    measure("identity", lambda: capture_identity(Path(out)))
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
    resolution = measure("lake-resolution", lambda: json.loads(subprocess.check_output(
        ["lake", "--log-level=error", "run", "feedback-context"], text=True)))
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
            "configuration_sha256": measure("dependency-configuration",
                lambda: digest(configuration.read_bytes()),
                package=package["key"], path=str(configuration)),
            **measure("dependency-git", lambda: git_state(path),
                package=package["key"], path=str(path))})
    inputs = sources.copy()
    from acceptance_inputs import CHECKPOINT, parse_selection
    acceptance_manifest, acceptance = parse_selection(stems)
    if acceptance_manifest is not None:
        inputs.append(acceptance_manifest)
    inputs += [item["source"] for item in acceptance]
    if any(item["kind"] == "extension" for item in acceptance):
        inputs.append(str(CHECKPOINT))
    inputs += ["lean-toolchain", "lake-manifest.json", "lakefile.lean"]

    installed = Path(os.environ.get("CAS_LEAVES", ".lake/packages/cas_leaves"))
    if installed.suffix != ".json":
        installed /= "leaves.json"
    inputs.append(str(installed))
    if "CAS_REALIZATION_PROFILE" in os.environ:
        inputs.append(os.environ["CAS_REALIZATION_PROFILE"])
    input_hashes = measure("input-fingerprint", lambda: {
        name: digest(Path(name).read_bytes()) if Path(name).is_file() else None for name in inputs})
    source = measure("source-fingerprint", lambda: git_state(checkout), path=str(checkout))
    environment = measure("toolchain-environment", lambda: {
        "host": platform.node(), "system": platform.platform(), "machine": platform.machine(),
        "python": platform.python_version(),
        "lean": read_json(Path(out))["environment"]["lean"],
        "image_digest": os.environ["CAS_FEEDBACK_IMAGE_DIGEST"],
        "lake": subprocess.check_output(["lake", "--version"], text=True).strip(),
        "selectors": {key: os.environ[key] for key in ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SYSROOT",
            "CAS_LEAVES", "CAS_REALIZATION_PROFILE", "CAS_LEAF_CONTRACT_PATH", "CAS_SAGE_PYTHON",
            "CAS_GAP_PYTHON") if key in os.environ}})
    workload = {"targets": targets, "acceptance": stems, "inputs": input_hashes,
                "source": source, "dependencies": dependencies, "resolution": resolution,
                "environment": environment}
    entry = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "kind": kind,
        "run": Path(out).parent.name, "revision": source["revision"], "dirty": source["dirty"],
        "reason": reason, "command": argv[cursor:], "sources": sources, "log": log,
        "workload": measure("workload-fingerprint",
            lambda: digest(json.dumps(workload, sort_keys=True).encode())), **workload}
    prior = read_json(Path(out))
    entry["utc"] = prior["utc"]
    entry["started_monotonic_ns"] = prior["started_monotonic_ns"]
    entry["parent_run"] = prior.get("parent_run")
    entry["acceptance_files"] = prior.get("acceptance_files", [])
    entry["context"] = out
    entry["context_status"] = "complete"
    measure("context-publication", lambda: atomic_json(Path(out), entry))
    measure("journal-publication", lambda: append_record(Path(out).parent / "events.jsonl",
                  {**identity(entry), "event": "run.context", "context_status": "complete"}))
    preparation_finished = time.monotonic_ns()
    try:
        atomic_json(Path(out).with_name("context-preparation.json"), {
            "context": out, "started_monotonic_ns": preparation_started,
            "finished_monotonic_ns": preparation_finished, "complete": True, "spans": spans,
        })
    except Exception as error:
        try:
            print(f"feedback: preparation timing could not be recorded: {error}", file=sys.stderr)
        except OSError:
            pass


def step_start(argv: list[str]) -> None:
    context_file, phase, source, started, shared = argv[1:6]
    context = read_json(Path(context_file))
    record = {
        **identity(context), "event": "module.started" if phase == "execution" else "phase.started",
        "phase": phase, "step": f"{phase}:{started}", "utc": utc_at(context, int(started)),
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


def execute_lean(command: dict) -> None:
    environment = os.environ.copy()
    for key, value in command["env"]:
        if value is None:
            environment.pop(key, None)
        else:
            environment[key] = value
    for name in ("SIGPIPE", "SIGXFZ", "SIGXFSZ"):
        signum = getattr(signal, name, None)
        if signum is not None:
            signal.signal(signum, signal.SIG_DFL)
    os.execvpe(command["cmd"], [command["cmd"], *command["args"]], environment)


def execute_probe(argv: list[str]) -> None:
    with tempfile.TemporaryDirectory(prefix="lean-cas-probe-") as temporary:
        output = Path(temporary) / "command.json"
        result = subprocess.run(["lake", "run", "feedback-lean", argv[1], str(output)])
        if result.returncode:
            raise SystemExit(result.returncode if result.returncode > 0 else 128 - result.returncode)
        command = read_json(output)
    execute_lean(command)


def execute_prepared(argv: list[str]) -> None:
    context_file, worker = argv[1:3]
    run = Path(context_file).parent
    prepared = read_json(run / "prepared-workers.json")
    command = prepared["commands"][int(worker)]
    source = run / f"worker{worker}.lean"
    if (prepared["context"] != context_file or command["worker"] != int(worker)
            or command["source"] != str(source)
            or command["contents"].encode("utf-8") != source.read_bytes()):
        raise ValueError("prepared worker does not match its current context and source")
    execute_lean(command)


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


def collect_computations(context_file: Path, shared_setup_seconds: float) -> dict:
    """Derive records only from the statement runner's durable events, never report rows."""
    context = read_json(context_file)
    run = context_file.parent
    computations: dict[str, dict] = {}
    statements: dict[tuple[str, int], dict] = {}
    parse_failures: dict[tuple[str, int], dict] = {}
    children: dict[tuple[str, int], dict] = {}
    files: dict[tuple[str, str], dict] = {}
    session_workers: dict[str, str | None] = {}
    session_steps: dict[str, str | None] = {}
    session_sources: dict[str, str | None] = {}
    preparations: dict[str, dict] = {}
    beginnings: dict[tuple[str, int], dict] = {}
    scope_stops: list[dict] = []
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


                    expected_sequence = event["sequence"] + 1
                    if name == "session.started":
                        worker = data.get("feedbackWorker")
                        if worker is not None and (not isinstance(worker, str) or not worker):
                            raise ValueError("invalid declared feedback worker")
                        session_workers[session] = worker
                        for field in ("feedbackStep", "feedbackSource"):
                            if data.get(field) is not None and not isinstance(data[field], str):
                                raise ValueError(f"invalid declared {field}")
                        session_steps[session] = data.get("feedbackStep") or None
                        session_sources[session] = data.get("feedbackSource") or None
                    elif name == "session.prepared":
                        if session in preparations:
                            raise ValueError("duplicate session preparation boundary")
                        for field in ("startedMonotonicMilliseconds", "milliseconds"):
                            if type(data[field]) is not int or data[field] < 0:
                                raise ValueError(f"invalid session preparation {field}")
                        if (data["startedMonotonicMilliseconds"] + data["milliseconds"] >
                                event["monotonicMilliseconds"]):
                            raise ValueError("session preparation ends before its measured work")
                        preparations[session] = event
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
                        if name == "computation.started" and (
                                type(data["startedMonotonicMilliseconds"]) is not int or
                                not 0 <= data["startedMonotonicMilliseconds"] <= event["monotonicMilliseconds"]):
                            raise ValueError("invalid original computation start")
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
                    elif name in {"statement.started", "statement.finished", "statement.interrupted"}:
                        if name == "statement.started":
                            if not isinstance(data["source"], str) or not isinstance(data["position"], dict):
                                raise ValueError("invalid original statement source or position")
                            if (type(data["startedMonotonicMilliseconds"]) is not int or
                                    not 0 <= data["startedMonotonicMilliseconds"] <=
                                    event["monotonicMilliseconds"]):
                                raise ValueError("invalid original statement start")
                            sequence, field = event["sequence"], "start"
                        else:
                            if not event["parents"]:
                                raise ValueError("statement terminal event lost its owning start")
                            sequence = event["parents"][-1]
                            field = "completion" if name == "statement.finished" else "interruption"
                            if type(data["milliseconds"]) is not int or data["milliseconds"] < 0:
                                raise ValueError("invalid statement execution time")
                            if field == "completion" and (
                                    not isinstance(data["kind"], str) or
                                    any(type(data[key]) is not bool for key in
                                        ("fails", "published", "retainsSetup"))):
                                raise ValueError("statement timing lost its actual result")
                        if (type(data["cumulativeSetupMilliseconds"]) is not int or
                                data["cumulativeSetupMilliseconds"] < 0):
                            raise ValueError("invalid retained statement setup")
                        item = statements.setdefault((session, sequence),
                            {"source_log": str(log), "session": session})
                        if field in item or (field != "start" and
                                ("completion" in item or "interruption" in item)):
                            raise ValueError(f"duplicate statement {field} at {session}/{sequence}")
                        item[field] = event
                    elif name == "statement.parseFailed":
                        if not isinstance(data["source"], str) or not isinstance(data["position"], dict):
                            raise ValueError("invalid rejected statement source or position")
                        for field in ("startedMonotonicMilliseconds", "milliseconds",
                                      "cumulativeSetupMilliseconds"):
                            if type(data[field]) is not int or data[field] < 0:
                                raise ValueError(f"invalid rejected statement {field}")
                        if (data["startedMonotonicMilliseconds"] + data["milliseconds"] >
                                event["monotonicMilliseconds"]):
                            raise ValueError("rejected statement ends before its measured work")
                        if (data["kind"] != "invalid" or data["stratum"] != "invalid" or
                                data["fails"] is not True or any(data[key] is not False for key in
                                ("attempted", "published", "retainsSetup"))):
                            raise ValueError("rejected statement timing lost its actual failure")
                        parse_failures[(session, event["sequence"])] = {
                            "source_log": str(log), "session": session, "completion": event}
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
                            if (type(data["startedMonotonicMilliseconds"]) is not int or
                                    not 0 <= data["startedMonotonicMilliseconds"] <= event["monotonicMilliseconds"]):
                                raise ValueError("invalid original nested statement start")
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
                    elif name == "statement.scope.stopped":
                        scope_stops.append(event)
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
    process_steps = {}
    invalid_steps = set()
    for path in (run / "steps").glob("*.json"):
        try:
            step = read_json(path)
            if not isinstance(step["phase"], str) or not isinstance(step["step"], str):
                raise ValueError("invalid recorded phase")
            if step["step"] in process_steps:
                invalid_steps.add(step["step"])
                raise ValueError(f"duplicate original process step {step['step']}")
            started = step["started_monotonic_ns"]
            if type(started) is not int or started < 0:
                invalid_steps.add(step["step"])
                raise ValueError(f"invalid original process start for {step['step']}")
            process_steps[step["step"]] = step
        except (json.JSONDecodeError, KeyError, TypeError, ValueError) as error:
            malformed.append(f"{path}: {error}")
    first_sessions = {}
    for session, preparation in preparations.items():
        step = session_steps.get(session)
        if step is not None:
            entered = preparation["data"]["startedMonotonicMilliseconds"]
            first_sessions[step] = min(first_sessions.get(step, entered), entered)
    process_setup = {}
    for step, entered in first_sessions.items():
        original = process_steps.get(step)
        if original is None or step in invalid_steps:
            malformed.append(f"process {step} has no unique recorded startup boundary")
            invalid_steps.add(step)
        elif entered < original["started_monotonic_ns"] // 1_000_000:
            malformed.append(f"process {step} entered a session before its recorded start")
            invalid_steps.add(step)
        else:
            process_setup[step] = (entered - original["started_monotonic_ns"] // 1_000_000) / 1000
    for session in session_steps:
        step = session_steps[session]
        worker = session_workers.get(session)
        original = process_steps.get(step)
        if (step in invalid_steps or (worker is not None and original is not None and
                original["phase"] != f"acceptance-worker{worker}")):
            invalid_sessions.add(session)
    wrapper_starts = {(item["session"], item["start"]["sequence"])
                      for item in computations.values() if "start" in item}
    for (session, sequence), item in statements.items():
        start = item.get("start")
        if start is None:
            malformed.append(f"statement terminal event {session}/{sequence} has no original start")
            continue
        if any((session, parent) in wrapper_starts for parent in start["parents"]):
            continue
        computations[f"{session}/statement/{sequence}"] = {**item, "direct": True}
    for (session, sequence), item in parse_failures.items():
        if any((session, parent) in wrapper_starts for parent in item["completion"]["parents"]):
            continue
        computations[f"{session}/parse/{sequence}"] = {**item, "direct": True, "parse_failure": True}
    rows = []
    root_starts = {}
    for key, item in computations.items():
        start, completion = item.get("start"), item.get("completion")
        terminal = completion or item.get("interruption")
        data = (terminal or start)["data"]
        source_data = (start or terminal)["data"]
        session = item["session"]
        direct = item.get("direct", False)
        setup = float(data["cumulativeSetupMilliseconds"] / 1000)
        agreed = completion is not None and (start is not None or item.get("parse_failure", False))
        step = session_steps.get(session)
        original_step = process_steps.get(step, {})
        row_shared_setup = (original_step["shared_setup_seconds"] if original_step.get("phase") == "build"
                            else shared_setup_seconds)
        if direct:
            execution = float(data["milliseconds"] / 1000) if terminal else None
            seconds = execution + setup if execution is not None else None
            file = session_sources.get(session) or source_data["position"].get("file")
            source_hash = original_step.get("input_sha256") if original_step.get("source") == file else None
            source_hash = source_hash or context["inputs"].get(file)
            if not file or source_hash is None:
                malformed.append(f"statement {key} has no recorded source input")
                agreed = False
            if (original_step.get("source") and session_sources.get(session) and
                    original_step["source"] != session_sources[session]):
                malformed.append(f"statement {key} changed its declared module source")
                agreed = False
            if (original_step.get("source") == file and "final_input_sha256" in original_step and
                    original_step["final_input_sha256"] != source_hash):
                malformed.append(f"statement {key} changed its source input during execution")
                agreed = False
            ordinal = (start or terminal)["sequence"]
            statement_id = f"(statement) {source_data['source']}"
            file_run = None
            outcome = data if completion else None
            if start and terminal:
                agreed = agreed and source_data["cumulativeSetupMilliseconds"] == data["cumulativeSetupMilliseconds"]
                agreed = agreed and (source_data["startedMonotonicMilliseconds"] + data["milliseconds"] <=
                                     terminal["monotonicMilliseconds"])
        else:
            seconds = float(data["milliseconds"] / 1000) if completion else None
            execution = float(data["executionMilliseconds"] / 1000) if completion else None
            file, file_run, source_hash = data["file"], data["fileRun"], data["sourceSha256"]
            ordinal, statement_id = data["ordinal"], data.get("id")
            outcome = data["result"] if completion else None
        if agreed and not direct:
            agreed = all(start["data"][field] == data[field] for field in
                         ("computation", "fileRun", "file", "ordinal", "sourceSha256",
                          "cumulativeSetupMilliseconds"))
            agreed = agreed and completion["monotonicMilliseconds"] >= start["monotonicMilliseconds"]
        if start and completion and not agreed:
            malformed.append(f"computation {key} changed its original statement, input, or setup")
        worker = session_workers.get(session)
        shared_worker = process_setup.get(step)
        preparation = preparations.get(session)
        shared_session = float(preparation["data"]["milliseconds"] / 1000) if preparation else None
        if preparation is None:
            malformed.append(f"session {session} has no recorded preparation boundary")
        if step is None:
            malformed.append(f"session {session} has no declared process step")
        row = {
            **identity(context), **item, "unit": "statement", "computation": key,
            "parent_computation": None, "root_computation": key,
            "file": file, "file_run": file_run, "worker": worker, "step": step,
            "ordinal": ordinal, "id": statement_id,
            "input_sha256": source_hash, "seconds": seconds,
            "statement_sha256": hashlib.sha256(source_data["source"].encode()).hexdigest() if "source" in source_data else None,
            "execution_seconds": execution, "setup_seconds": setup,
            "shared_setup_seconds": row_shared_setup,
            "shared_worker_setup_seconds": shared_worker,
            "shared_session_setup_seconds": shared_session,
            "session_preparation": preparation,
            "shared_setup": {"context": str(context_file), "phases": ["preparation", "build"],
                             "before_step": step if original_step.get("phase") == "build" else None},
            "inclusive_seconds": (seconds + row_shared_setup + shared_worker + shared_session
                                  if all(value is not None for value in
                                         (seconds, shared_worker, shared_session)) else None),
            "outcome": outcome,
            "complete": (agreed and shared_worker is not None and shared_session is not None
                         and session not in invalid_sessions),
        }
        rows.append(row)
        if start:
            root_starts[(item["session"], start["sequence"])] = row



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
            malformed.append(f"nested computation {child_key} has no recorded root")
            continue
        parent_key = next((key for key in ancestors if key in children or key in root_starts), None)
        if parent_key is None:
            malformed.append(f"nested computation {child_key} lost its actual parent")
            continue
        nested_roots[child_key] = root_key
        nested_parents[child_key] = parent_key
        child_started = start["data"]["startedMonotonicMilliseconds"]
        first_children[parent_key] = min(first_children.get(parent_key, child_started), child_started)

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
            parent_start = parent["start"]["data"].get(
                "startedMonotonicMilliseconds", parent["start"]["monotonicMilliseconds"])
            preflight = (first_children[parent_key] - parent_start) / 1000
            if preflight < 0:
                malformed.append(f"nested computation {child_key} precedes its parent")
            elif parent["setup_seconds"] is not None:
                setup = parent["setup_seconds"] + preflight + preceding
        else:
            malformed.append(f"nested computation {child_key} has no recorded containing scope")
        terminal_ordered = terminal is None or (
            start["data"]["startedMonotonicMilliseconds"] + terminal["data"]["milliseconds"] <=
            terminal["monotonicMilliseconds"])
        if not terminal_ordered:
            malformed.append(f"nested computation {child_key} has a terminal event before its start")
        execution = float(terminal["data"]["milliseconds"] / 1000) if terminal else None
        seconds = execution + setup if execution is not None and setup is not None else None
        enclosing = root["outcome"]
        key = f"{item['session']}/child/{start['sequence']}"
        row = {
            **identity(context), **item, "unit": "nested_statement", "computation": key,
            "parent_computation": parent["computation"] if parent else None,
            "root_computation": root["computation"],
            "file": root["file"], "file_run": root["file_run"], "worker": root["worker"],
            "step": root["step"],
            "ordinal": start["data"]["ordinal"], "id": start["data"]["id"],
            "input_sha256": root["input_sha256"], "seconds": seconds,
            "execution_seconds": execution, "setup_seconds": setup,
            "enclosing_preflight_seconds": preflight, "preceding_setup_seconds": preceding,
            "shared_setup_seconds": root["shared_setup_seconds"],
            "shared_worker_setup_seconds": root["shared_worker_setup_seconds"],
            "shared_session_setup_seconds": root["shared_session_setup_seconds"],
            "session_preparation": root["session_preparation"],
            "shared_setup": root["shared_setup"],
            "inclusive_seconds": (seconds + root["shared_setup_seconds"] + root["shared_worker_setup_seconds"] +
                                  root["shared_session_setup_seconds"]
                                  if all(value is not None for value in (seconds,
                                      root["shared_worker_setup_seconds"], root["shared_session_setup_seconds"]))
                                  else None),
            "outcome": completion["data"] if completion else None,
            "enclosing_outcome": enclosing,
            "enclosing_published": enclosing["published"] if enclosing is not None else None,
            "complete": (completion is not None and root["complete"] and setup is not None
                         and terminal_ordered),
        }
        rows.append(row)
        scoped_rows[child_key] = row

    complete = not malformed and all(row["complete"] and
        (row["file_run"] is None or (row["session"], row["file_run"]) in files) for row in rows)
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
        terminal = finish or failure
        file_seconds = ((terminal["monotonicMilliseconds"] - begin["monotonicMilliseconds"]) / 1000
                        if terminal is not None and begin is not None else None)
        matched = matched and (file_seconds is None or file_seconds >= 0)
        matched = matched and session not in invalid_sessions
        complete = complete and matched
        file_records.append({"file": file, "file_run": file_run, "session": session, "statements": count,
                             "executed": executed, "records": len(starts), "nested_records": len(nested),
                             "total_records": len(file_rows), "complete": matched,
                             "begin": begin, "start": start, "completion": finish,
                             "failure": failure, "failure_seconds": failure_seconds,
                             "seconds": file_seconds, "worker": session_workers.get(session),
                             "step": session_steps.get(session),
                             "utc_start": utc_at(context, begin["monotonicMilliseconds"] * 1000000)
                                 if begin is not None else None})
    for key, begin in beginnings.items():
        if key not in recorded_beginnings:
            complete = False
            file_records.append({"file": begin["data"]["file"], "file_run": None,
                                 "session": key[0], "statements": None, "executed": None,
                                 "records": 0, "nested_records": 0, "total_records": 0,
                                 "complete": False, "begin": begin, "start": None,
                                 "completion": None, "failure": None, "seconds": None,
                                 "worker": session_workers.get(key[0]), "step": session_steps.get(key[0]),
                                 "utc_start": utc_at(context, begin["monotonicMilliseconds"] * 1000000)})


    source_report = reconcile(file_records, rows, scope_stops)
    source_report_path = run / "source-occurrences.json"
    atomic_json(source_report_path, source_report)
    source_occurrences = {"path": str(source_report_path), "sha256": digest(source_report_path),
                          "complete": source_report["complete"], "files": len(source_report["files"])}
    complete = complete and source_report["complete"]
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
              "scope_stops": scope_stops, "source_occurrences": source_occurrences,
              "record_file": str(run / "computations.jsonl")}
    atomic_json(run / "computation-summary.json", result)
    return result


def finish_feedback(argv: list[str]) -> int:
    (records, context_file, status, limit, total, preparation, build, execution, acceptance,
     bs, es, acs, attempted, signal) = argv[1:15]
    attempted_sources = argv[15:]
    context_path = Path(context_file)
    entry = read_json(context_path)
    seconds = int(total) / 1e9
    over = entry["kind"] == "loop" and seconds > int(limit)
    execution_result = int(status)
    result = execution_result or (1 if over else 0)
    interrupted = bool(signal)
    phases = {name: {"seconds": int(elapsed) / 1e9, "status": int(code) if code else None}
              for name, elapsed, code in (("build", build, bs), ("execution", execution, es),
                                         ("acceptance", acceptance, acs))}
    phase_steps = {name: [] for name in phases}
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
        if step["phase"] in phase_steps:
            phase_steps[step["phase"]].append(step)
        if (step["phase"] == "execution" and step["complete"] and
                step["input_sha256"] != step.get("final_input_sha256")):
            result = result or 1
            print(f"feedback: selected module changed during execution: {step['source']}; "
                  f"initial sha256 {step['input_sha256']}; final sha256 {step.get('final_input_sha256')}",
                  file=sys.stderr)
    for name, steps in phase_steps.items():
        if steps:
            phases[name] = {"seconds": sum(step["seconds"] for step in steps),
                            "status": next((step["status"] for step in sorted(
                                steps, key=lambda step: step["started_monotonic_ns"])
                                if step["status"]), 0)}
    shared = int(preparation) / 1e9 + phases["build"]["seconds"]
    for source in entry["sources"]:
        if source not in attempted_sources:
            append_record(context_path.parent / "events.jsonl", {
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
        "finished_utc": utc(), "complete": not interrupted and computations["complete"],
        "computations": computations, "source_occurrences": computations["source_occurrences"],
        "preparation_seconds": int(preparation) / 1e9,
        "phases": phases, "interruption_signal": signal or None,
    })
    summary = (f"{entry['kind']}: execution status {execution_result}; status {result} "
               f"in {seconds:.3f} s; log {entry['log']}.gz")
    if computations["source_occurrences"]["files"]:
        summary += f"; source occurrences {computations['source_occurrences']['path']}"
    if over:
        summary += f"\nOVER THE LIMIT: the {limit}-second development loop needs repair."
    atomic_json(context_path.parent / "result.json", entry)
    print(summary)
    return result


def finalize_feedback(argv: list[str]) -> int:
    records, context_file, drain_status = argv[1:4]
    context_path = Path(context_file)
    context = read_json(context_path)
    run = context_path.parent
    entry = read_json(run / "result.json")
    entry["status"] = entry["status"] or int(drain_status)
    if int(drain_status):
        entry["complete"] = False
        entry["log_writer_status"] = int(drain_status)
    log_path, log_sha256 = compress_log(Path(entry["log"]))
    context["log"] = entry["log"] = log_path
    entry["log_sha256"] = log_sha256
    atomic_json(context_path, context)
    atomic_json(run / "result.json", entry)
    steps = [read_json(path) for path in (run / "steps").glob("*.json")]
    for source in dict.fromkeys(context["sources"]):
        observed = sorted((step for step in steps
                           if step["phase"] == "execution" and step["source"] == source),
                          key=lambda step: step["started_monotonic_ns"])
        if observed:
            status = ("interrupted" if entry["interruption_signal"] and
                      any(not step["complete"] for step in observed) else
                      "pass" if not int(drain_status) and all(step["complete"] and step["status"] == 0
                                    and step.get("input_sha256") == step.get("final_input_sha256")
                                    for step in observed) else "fail")
            start = observed[0]["utc"]
            seconds = sum(step["seconds"] for step in observed)
            input_sha256 = observed[0]["input_sha256"]
        else:
            status = "interrupted" if entry["interruption_signal"] else "fail"
            start, seconds = context["utc"], 0
            input_sha256 = context["inputs"].get(source)
        append_record(Path("timing/modules.jsonl"), terminal_row(
            context, target=source.removesuffix(".lean").replace("/", "."),
            input_sha256=input_sha256, utc_start=start, seconds=seconds,
            status=status, log_path=log_path, log_sha256=log_sha256))
    if not (run / "acceptance-child.json").is_file():
        for selected in context.get("acceptance_files", []):
            source = selected["source"]
            append_record(Path("timing/acceptance.jsonl"), terminal_row(
                context, target=source, input_sha256=context["inputs"].get(source),
                utc_start=context["utc"], seconds=0,
                status="interrupted" if entry["interruption_signal"] else "fail",
                log_path=log_path, log_sha256=log_sha256))
    append_record(Path(records), entry)
    append_record(run / "events.jsonl",
                  {**identity(entry), "event": "run.finished", "status": entry["status"],
                   "seconds": entry["seconds"], "finished_utc": entry["finished_utc"],
                    "source_occurrences": entry["source_occurrences"],
                   "interruption_signal": entry["interruption_signal"]})
    return entry["status"]


if __name__ == "__main__":
    command = sys.argv[1]
    arguments = [sys.argv[0], *sys.argv[2:]]
    if command == "begin":
        begin(arguments)
    elif command == "identity":
        capture_identity(Path(arguments[1]))
    elif command == "context":
        capture_context(arguments)
    elif command == "step-start":
        step_start(arguments)
    elif command == "execute-prepared":
        execute_prepared(arguments)
    elif command == "probe":
        execute_probe(arguments)
    elif command == "step-finish":
        step_finish(arguments)
    elif command == "finish":
        raise SystemExit(finish_feedback(arguments))
    elif command == "finalize":
        raise SystemExit(finalize_feedback(arguments))
    else:
        raise SystemExit(f"unknown timing operation: {command}")
