#!/usr/bin/env python3
"""Pin the public protocol fixture environment around the focused build runner."""
import json
import os
import sys

from focused_build import run
from runtime_state import KERNEL, RUNTIME, record, selected_packages, sha256, write


def fixture_hashes(contract):
    files = sorted((KERNEL / "CasAcceptance/Strata").glob("*.py"))
    files.append(contract / "python/cas_port.py")
    return {str(path): sha256(path) for path in files}


def main():
    contract = selected_packages()["cas_leaf_contracts"]
    before = fixture_hashes(contract)
    os.environ["CAS_LEAF_CONTRACT_PATH"] = str(contract)
    os.environ["PYTHONPATH"] = str(contract / "python") + (
        os.pathsep + os.environ["PYTHONPATH"] if os.environ.get("PYTHONPATH") else "")
    os.environ["CAS_OWNERSHIP_PROTOCOL_DIR"] = str(KERNEL / "CasAcceptance/Strata")
    result = run(sys.argv[1:])
    after = fixture_hashes(contract)
    changed = sorted(path for path in set(before) | set(after) if before.get(path) != after.get(path))
    from pathlib import Path
    sidecar = Path(result["receipt"]).with_suffix(".protocol.json")
    write(sidecar, {
        "purpose": "Fixture framing provenance only; no mathematical correctness claim",
        "buildReceipt": result["receipt"], "wrapper": record(__file__),
        "contract": str(contract), "fixtureHashesBefore": before,
        "fixtureHashesAfter": after, "changedFixtures": changed,
        "environment": {key: os.environ.get(key) for key in (
            "CAS_LEAF_CONTRACT_PATH", "PYTHONPATH", "CAS_OWNERSHIP_PROTOCOL_DIR")},
    })
    print(json.dumps({"protocolReceipt": str(sidecar), "changedFixtures": changed}))
    return result["exit"] or (7 if changed else 0)


if __name__ == "__main__":
    raise SystemExit(main())
