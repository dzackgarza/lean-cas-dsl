#!/usr/bin/env python3
"""Check out the development chain for the gates in CI: `lean_categories`, `cas_leaf_contracts`
and `cas_leaves`, each at the revision `lake-manifest.json` pins, with its full history, under
`.lake/packages/` (where `scripts/check_authorship.py` reads them)."""

import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHAIN = ("lean_categories", "cas_leaf_contracts", "cas_leaves")


def main() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = ROOT / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    for entry in manifest["packages"]:
        if entry["name"] not in CHAIN:
            continue
        target = packages / entry["name"]
        subprocess.run(["git", "clone", "--quiet", entry["url"], str(target)], check=True)
        subprocess.run(["git", "-C", str(target), "checkout", "--quiet", entry["rev"]], check=True)


if __name__ == "__main__":
    main()
