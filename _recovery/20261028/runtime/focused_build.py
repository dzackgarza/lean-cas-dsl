#!/usr/bin/env python3
"""Run explicit local targets with before/after source and real artifact checks.

This is reconstructed engineering tooling, not a protected acceptance operation.
No assertion, Lean option, heartbeat limit, or dependency selection is changed.
"""
import json
from pathlib import Path
import subprocess
import sys
import time

from artifact_consistency import audit
from runtime_state import EVIDENCE, KERNEL, RUNTIME, configuration, environment, owned_sources, record, source_state, write


def run(targets):
    if not targets or any(not target or target.startswith("-") for target in targets):
        raise ValueError("Explicit focused target names are required")
    identifier = str(time.time_ns())
    receipt = EVIDENCE / ("focused-build-" + identifier + ".json")
    log = receipt.with_suffix(".log")
    before = source_state()
    sources_before = owned_sources()
    config_before = configuration()
    command = ["bash", str(RUNTIME / "lake.sh"), "build", *targets]
    result = {
        "purpose": "Focused engineering build; no acceptance authority inferred",
        "reconstruction": "External runner reconstructed after the 2026-10-28 workspace reset",
        "targets": targets, "command": command, "status": "running",
        "started": time.time(), "sourceTupleBefore": before,
        "ownedSourcesBefore": sources_before, "configurationBefore": config_before,
        "environment": {key: environment().get(key) for key in (
            "LEAN_NUM_THREADS", "MATHLIB_CACHE_DIR", "CAS_LEAF_CONTRACT_PATH", "PYTHONPATH", "CAS_OWNERSHIP_PROTOCOL_DIR")},
    }
    write(receipt, result)
    print(json.dumps({"receipt": str(receipt), "log": str(log), "targets": targets}), flush=True)
    started = time.monotonic()
    preflight = audit()
    result["artifactAuditBefore"] = preflight["receipt"]
    if preflight["exit"]:
        log.write_text("Build not started: actual artifact hash preflight failed.\n")
        result.update(status="blocked", leanExit=None, exit=4)
    else:
        with log.open("x") as output:
            process = subprocess.Popen(command, cwd=KERNEL, env=environment(),
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                       text=True, bufsize=1)
            for line in process.stdout:
                output.write(line)
                output.flush()
                print(line, end="", flush=True)
            lean_exit = process.wait()
        postflight = audit()
        result.update(status="completed", leanExit=lean_exit,
                      artifactAuditAfter=postflight["receipt"],
                      exit=lean_exit if lean_exit else (5 if postflight["exit"] else 0))
    after = source_state()
    sources_after = owned_sources()
    config_after = configuration()
    result.update(
        elapsedSeconds=time.monotonic() - started,
        sourceTupleAfter=after, ownedSourcesAfter=sources_after,
        configurationAfter=config_after,
        sourceTupleChanged=before != after,
        changedDuringBuild=sorted(key for key in set(sources_before) | set(sources_after)
                                  if sources_before.get(key) != sources_after.get(key)),
        configurationChanged=config_before != config_after,
        log=record(log), receipt=str(receipt),
    )
    if result["sourceTupleChanged"] or result["changedDuringBuild"] or result["configurationChanged"]:
        result["exit"] = result["exit"] or 6
    write(receipt, result)
    print(json.dumps({key: result.get(key) for key in (
        "receipt", "status", "leanExit", "exit", "elapsedSeconds", "sourceTupleChanged", "changedDuringBuild")}), flush=True)
    return result


if __name__ == "__main__":
    raise SystemExit(run(sys.argv[1:])["exit"])
