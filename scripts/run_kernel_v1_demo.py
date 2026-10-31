#!/usr/bin/env python3
"""Run the editable V1 examples through the existing CAS harness.

This is invocation and report checking, not a mathematical evaluator. It uses
an explicit nonoverlapping leaf configuration and never builds, downloads, or
updates dependencies. See examples/kernel-v1.md for prerequisites and scope.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SET_SELECTION = (
    ("lim.sets.pullback", "cat.sets", "sage-set-limits"),
    ("meth.cardinality", "cat.sets", "sage-set-limits"),
)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def demo_assertions(suite: Path) -> dict[str, str]:
    """Collect demo IDs before execution; never edit the protected inventory."""
    files = sorted(suite.glob("*.cas")) if suite.is_dir() else [suite]
    assertions = {}
    for path in files:
        ids = re.findall(r'^test\s+([^\s]+)\s+"', path.read_text(encoding="utf-8"), re.MULTILINE)
        if not ids:
            raise ValueError(f"no named demo assertions in {path}")
        for identity in ids:
            if identity in assertions:
                raise ValueError(f"duplicate demo assertion: {identity}")
            assertions[identity] = str(path)
    if not assertions:
        raise ValueError(f"no .cas demo files in {suite}")
    return assertions


def selected_manifest(diagnostic: Path, existing: Path) -> dict:
    """Compose a caller-selected configuration using the public manifest fields."""
    backends = {}
    registrations = []
    for path, selection in ((diagnostic, None), (existing, SET_SELECTION)):
        source = read_json(path)
        rows = source.get("registrations", [])
        if not isinstance(rows, list):
            raise ValueError(f"registrations must be an array: {path}")
        if selection is not None:
            selected = []
            for operation, form, backend in selection:
                matches = [row for row in rows if row.get("operation") == operation
                           and row.get("input") == form and row.get("backend") == backend]
                if len(matches) != 1:
                    raise ValueError(f"expected one registration for {operation} on {form} "
                                     f"from {backend} in {path}; found {len(matches)}")
                selected.extend(matches)
            rows = selected
        declared = source.get("backends", [])
        if not isinstance(declared, list):
            raise ValueError(f"backends must be an array: {path}")
        needed = {row["backend"] for row in rows}
        for name in sorted(needed):
            matches = [item for item in declared if item.get("name") == name]
            if len(matches) != 1 or name in backends:
                raise ValueError(f"backend name is missing or not unique: {name} in {path}")
            backend = matches[0]
            command, args = backend["command"], backend.get("args", [])
            if not isinstance(command, str) or not isinstance(args, list) \
                    or not all(isinstance(arg, str) for arg in args):
                raise ValueError(f"invalid command/args for {name} in {path}")
            # The mixed manifest runs from a different directory. Rebase selected
            # script/file arguments at their ORIGINAL manifest, with no cwd/env
            # extension to the public schema. Executable names remain PATH names.
            if "/" in command and not Path(command).is_absolute():
                command = str((path.parent / command).absolute())
            rebased = []
            for arg in args:
                candidate = path.parent / arg
                if not arg.startswith("-") and not Path(arg).is_absolute() \
                        and candidate.is_file():
                    arg = str(candidate.absolute())
                elif not arg.startswith("-") and arg.endswith(".py") \
                        and not candidate.is_file():
                    raise ValueError(f"selected backend script does not exist: {candidate}")
                rebased.append(arg)
            backends[name] = {"name": name, "command": command, "args": rebased}
        for row in rows:
            if not all(isinstance(row.get(key), str) for key in ("operation", "input", "backend")):
                raise ValueError(f"invalid registration in {path}: {row}")
            registrations.append({key: row[key] for key in ("operation", "input", "backend")})
    addresses = [(row["operation"], row["input"]) for row in registrations]
    if len(addresses) != len(set(addresses)):
        raise ValueError("the selected manifest has duplicate operation/input registrations")
    return {"backends": list(backends.values()), "registrations": registrations}


def check_report(report: Path, assertions: dict[str, str]) -> bool:
    """Require complete holds results and completed dispatches in every workflow."""
    rows = read_json(report)
    if not isinstance(rows, list) or not rows:
        raise ValueError(f"report contains no results: {report}")
    seen = Counter()
    dispatches = Counter()
    problems = []
    for row in rows:
        if not isinstance(row, dict) or not isinstance(row.get("id"), str):
            problems.append("malformed report result")
            continue
        identity = row["id"]
        if identity in assertions:
            seen[identity] += 1
        elif not identity.startswith("(statement)"):
            problems.append(f"unexpected assertion: {identity}")
        if row.get("kind") != "holds" or row.get("fails") is not False:
            problems.append(f"{identity}: {row.get('kind', 'missing outcome')}: {row.get('detail', '')}")
        calls = row.get("dispatches", [])
        if not isinstance(calls, list):
            problems.append(f"{identity}: malformed dispatch list")
            continue
        completed = sum(isinstance(call, dict)
                        and isinstance(call.get("operation"), str)
                        and isinstance(call.get("backend"), str)
                        and "request" in call and "response" in call and "failure" not in call
                        for call in calls)
        if identity in assertions:
            dispatches[assertions[identity]] += completed
    for identity in assertions:
        if seen[identity] != 1:
            problems.append(f"{identity}: expected exactly one result, found {seen[identity]}")
    for file in sorted(set(assertions.values())):
        if dispatches[file] == 0:
            problems.append(f"{Path(file).name}: no completed backend dispatch was recorded")
    for problem in problems:
        print(f"FAIL: {problem}", file=sys.stderr)
    if problems:
        return False
    for file in sorted(set(assertions.values())):
        count = sum(value == file for value in assertions.values())
        print(f"{Path(file).name}: {count}/{count} holds; "
              f"{dispatches[file]} completed dispatches recorded")
    print(f"Report checks passed for {len(assertions)} assertions: {report}")
    return True


def executable(value: str, label: str) -> str:
    found = shutil.which(value)
    if found is None:
        raise ValueError(f"{label} executable was not found: {value}")
    return str(Path(found).absolute())


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--contract", default=os.environ.get("CAS_LEAF_CONTRACT_PATH"),
                        help="contract checkout containing python/cas_port.py; or CAS_LEAF_CONTRACT_PATH")
    parser.add_argument("--sage-python", default=os.environ.get("CAS_SAGE_PYTHON"),
                        help="installed Sage Python executable; or CAS_SAGE_PYTHON")
    parser.add_argument("--diagnostic-manifest", type=Path,
                        default=ROOT.parent / "lean-cas-dsl-leaves-diagnostic/diagnostics/v1/leaves.json")
    parser.add_argument("--leaves-manifest", type=Path,
                        default=ROOT.parent / "lean-cas-dsl-leaves/leaves.json")
    parser.add_argument("--suite", type=Path, default=ROOT / "examples/kernel-v1",
                        help=".cas file or directory; defaults to the four V1 examples")
    parser.add_argument("--output", type=Path, default=ROOT.parent / "kernel-v1-run",
                        help="generated configuration and reports, outside the source repository")
    parser.add_argument("--packages", type=Path,
                        help="external Lake package overrides, passed as --packages; never copied into the repo")
    parser.add_argument("--lake", default="lake", help="Lake executable for the existing built source")
    parser.add_argument("--prepare-only", action="store_true",
                        help="write the run configuration and notebook instructions without running Lean or Sage")
    parser.add_argument("--check-report", type=Path,
                        help="only validate an existing computing-mode report, e.g. from the notebook")
    return parser.parse_args()


def main() -> int:
    args = arguments()
    suite = args.suite.resolve()
    assertions = demo_assertions(suite)
    if args.check_report:
        return 0 if check_report(args.check_report.resolve(), assertions) else 1
    if not args.contract or not args.sage_python:
        raise ValueError("provide --contract and --sage-python, or set "
                         "CAS_LEAF_CONTRACT_PATH and CAS_SAGE_PYTHON")
    contract = Path(args.contract).resolve()
    if not (contract / "python/cas_port.py").is_file():
        raise ValueError(f"contract checkout has no python/cas_port.py: {contract}")
    sage = executable(args.sage_python, "Sage Python")
    diagnostic, existing = args.diagnostic_manifest.resolve(), args.leaves_manifest.resolve()
    manifest = selected_manifest(diagnostic, existing)
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        raise ValueError("choose --output outside the source repository")
    output.mkdir(parents=True, exist_ok=True)
    manifest_path, inventory, report = (output / name for name in
                                        ("leaves.json", "inventory.json", "report.json"))
    write_json(manifest_path, manifest)
    # This temporary list only prevents a missing demo result. It neither changes
    # nor substitutes for CasAcceptance/Permanent/admitted.json.
    write_json(inventory, {"assertions": {identity: {} for identity in assertions}})
    lake = args.lake if args.prepare_only else executable(args.lake, "Lake")
    harness = ROOT / ".lake/build/bin/cas-harness"
    if not args.prepare_only:
        executable(str(harness), "built CAS harness")
    lake_command = [lake]
    if args.packages:
        packages = args.packages.resolve()
        if not packages.is_file():
            raise ValueError(f"external Lake package manifest is missing: {packages}")
        lake_command.append(f"--packages={packages}")
    command = lake_command + ["env", str(harness),
                              "--suite", str(suite), "--manifest", str(manifest_path),
                              "--inventory", str(inventory), "--report", str(report),
                              "--computation-only"]
    source_paths = [diagnostic, existing, *map(Path, sorted(set(assertions.values())))]
    if args.packages:
        source_paths.append(args.packages.resolve())
    write_json(output / "inputs.json", {
        "suite": str(suite), "contract": str(contract), "sagePython": sage,
        "command": command, "sources": {str(path): digest(path) for path in source_paths},
    })
    print(f"Selected {len(manifest['registrations'])} registrations; "
          f"{len(assertions)} demo assertions. Configuration: {manifest_path}", flush=True)
    if args.prepare_only:
        print("Prepared only; no CAS computation, Sage import, or build has run.")
        print("Start the existing casdsl notebook kernel with these inherited variables:")
        for name, value in (("CAS_LEAF_CONTRACT_PATH", str(contract)),
                            ("CAS_SAGE_PYTHON", sage), ("CAS_LEAVES", str(manifest_path))):
            print(f"export {name}={shlex.quote(value)}")
        print("Notebook command (paths are absolute; adjust the notebook cell if needed):")
        quote = lambda path: json.dumps(str(path), ensure_ascii=False)
        print(f"#cas_tests {quote(suite)} manifest {quote(manifest_path)} "
              f"reporting {quote(output / 'notebook-report.json')} inventory {quote(inventory)} computing")
        return 0
    environment = os.environ.copy()
    environment["CAS_LEAF_CONTRACT_PATH"] = str(contract)
    environment["CAS_SAGE_PYTHON"] = sage
    environment["CAS_LEAVES"] = str(manifest_path)
    report.unlink(missing_ok=True)
    print("Running: " + shlex.join(command), flush=True)
    # Stream the existing harness output and retain it; impose no runtime budget.
    with (output / "execution.log").open("w", encoding="utf-8") as log:
        with subprocess.Popen(command, cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True, bufsize=1) as process:
            assert process.stdout is not None
            for line in process.stdout:
                print(line, end="", flush=True)
                log.write(line)
                log.flush()
            returncode = process.wait()
    valid = check_report(report, assertions)
    if returncode != 0:
        print(f"FAIL: CAS harness exited with status {returncode}; see {output / 'execution.log'}",
              file=sys.stderr)
    if valid and returncode == 0:
        print("Demo passed: every assertion holds and every workflow recorded completed dispatch.")
        return 0
    return 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"kernel-v1-demo: {error}", file=sys.stderr)
        sys.exit(1)
