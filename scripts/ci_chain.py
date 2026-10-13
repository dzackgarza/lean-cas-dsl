#!/usr/bin/env python3
"""Check out the development chain of a lean-cas-dsl checkout: `lean_categories`,
`cas_leaf_contracts` and `cas_leaves`, each at the revision its `lake-manifest.json` records, with
its full history, under `.lake/packages/` (where `custodian/verify.py` reads them,
and where `lake` builds them).

    ci_chain.py [checkout]        default: the checkout this script is in
"""

import json
import subprocess
import sys
from pathlib import Path

CHAIN = ("lean_categories", "cas_leaf_contracts", "cas_leaves")


def main() -> None:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = root / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    for entry in manifest["packages"]:
        if entry["name"] not in CHAIN:
            continue
        target = packages / entry["name"]
        subprocess.run(["git", "clone", "--quiet", "--", entry["url"], str(target)], check=True)
        subprocess.run(["git", "-C", str(target), "checkout", "--quiet", "--end-of-options",
                        entry["rev"]], check=True)


if __name__ == "__main__":
    main()
