#!/usr/bin/env python3
"""Compare real artifact bytes with Lake trace outputs; never trust .hash sidecars.

Reconstructed from the prior runner's retained specification. Missing outputs are
listed separately because failed builds can retain a trace without every output.
No source-to-artifact equivalence or acceptance authority is inferred here.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from runtime_state import EVIDENCE, KERNEL, RUNTIME, TOOLCHAIN, environment, record, selected_packages, write

DESCRIPTOR = re.compile(r"([0-9a-f]{16})\.(olean(?:\.private|\.server)?|ilean|ir(?:\.sig)?|c)")


def strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from strings(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from strings(item)


def expected_artifacts(roots, owned_only):
    expected, missing, conflicts, malformed = {}, [], [], []
    trace_records = []
    for label, root in roots.items():
        lib = root / ".lake/build/lib/lean"
        for trace in sorted(lib.rglob("*.trace")):
            relative = trace.relative_to(lib).with_suffix("")
            if owned_only and not relative.parts[0].startswith("Cas"):
                continue
            trace_records.append(record(trace))
            try:
                outputs = json.loads(trace.read_text()).get("outputs", {})
            except (ValueError, OSError) as error:
                malformed.append({"trace": str(trace), "error": str(error)})
                continue
            for descriptor in strings(outputs):
                match = DESCRIPTOR.fullmatch(descriptor)
                if not match:
                    malformed.append({"trace": str(trace), "output": descriptor})
                    continue
                digest, extension = match.groups()
                directory = root / ".lake/build/ir" if extension == "c" else lib
                path = Path(str(directory / relative) + "." + extension)
                if not path.is_file():
                    missing.append({"path": str(path), "expected": digest, "trace": str(trace)})
                    continue
                key = str(path.resolve())
                if key in expected and expected[key] != digest:
                    conflicts.append({"path": key, "first": expected[key], "second": digest})
                expected[key] = digest
    return expected, missing, conflicts, malformed, trace_records


def audit(scope="owned"):
    selected = selected_packages()
    roots = {"kernel": KERNEL, "contract": selected["cas_leaf_contracts"]}
    if scope == "dependencies":
        roots = selected
    elif scope == "all":
        roots = {"kernel": KERNEL, **selected}
    destination = EVIDENCE / ("artifact-consistency-" + str(time.time_ns()))
    destination.mkdir(parents=True)
    expected, missing, conflicts, malformed, traces = expected_artifacts(roots, scope == "owned")
    manifest = destination / "files.txt"
    manifest.write_text("\n".join(sorted(expected)) + ("\n" if expected else ""))
    command = [str(TOOLCHAIN / "bin/lean"), "--run", str(RUNTIME / "artifact_hash.lean"), str(manifest)]
    env = environment()
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SRC_PATH", None)
    log = destination / "hashes.log"
    started = time.monotonic()
    if expected:
        with log.open("x") as output:
            process = subprocess.run(command, cwd=RUNTIME, env=env, stdout=output, stderr=subprocess.STDOUT)
        code = process.returncode
    else:
        log.write_text("")
        code = 0
    actual = {}
    for line in log.read_text().splitlines():
        match = re.fullmatch(r"([0-9a-f]{16}) (.+)", line)
        if match:
            actual[match.group(2)] = match.group(1)
    mismatches = []
    for path, digest in expected.items():
        if path in actual and actual[path] != digest:
            mismatches.append({"path": path, "expected": digest, "actual": actual[path], **record(path)})
    unchecked = sorted(set(expected) - actual.keys())
    result = {
        "purpose": "Actual Lake binary hash consistency only; no source or acceptance claim",
        "scope": scope, "roots": {name: str(root) for name, root in roots.items()},
        "command": command, "elapsedSeconds": time.monotonic() - started,
        "hashProcessExit": code, "presentExpectedArtifacts": len(expected),
        "checkedArtifacts": len(actual), "mismatches": mismatches,
        "uncheckedArtifacts": unchecked, "missingArtifacts": missing,
        "conflictingExpectations": conflicts, "malformedTraces": malformed,
        "traces": traces, "hashOutput": record(log),
    }
    result["exit"] = 0 if not (code or mismatches or unchecked or conflicts or malformed) else 1
    path = destination / "receipt.json"
    result["receipt"] = str(path)
    write(path, result)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", choices=("owned", "dependencies", "all"), default="owned")
    result = audit(parser.parse_args().scope)
    print(json.dumps({key: result[key] for key in (
        "receipt", "exit", "scope", "presentExpectedArtifacts", "checkedArtifacts", "elapsedSeconds")}, indent=2))
    return result["exit"]


if __name__ == "__main__":
    raise SystemExit(main())
