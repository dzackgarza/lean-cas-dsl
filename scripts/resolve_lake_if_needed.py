#!/usr/bin/env python3
"""Resolve own-organisation Lake requires only when fetched main changed."""

import json
import subprocess
import sys
from pathlib import Path


OWN_REQUIRES = ("lean_categories", "cas_leaf_contracts", "nbdsl-worker")


def resolved_revisions(root: Path) -> dict[str, str]:
    manifest = json.loads((root / "lake-manifest.json").read_text())
    revisions = {}
    for entry in manifest["packages"]:
        name = entry["name"].removeprefix("«").removesuffix("»")
        if name in OWN_REQUIRES:
            revisions[name] = entry["rev"]
    missing = set(OWN_REQUIRES) - revisions.keys()
    if missing:
        raise RuntimeError(f"Lake manifest lacks own requires: {', '.join(sorted(missing))}")
    return revisions


def stale_requires(root: Path) -> list[str]:
    resolved = resolved_revisions(root)
    stale = []
    for name in OWN_REQUIRES:
        checkout = root / ".lake" / "packages" / name
        head = subprocess.check_output(
            ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
        if resolved[name] != head:
            stale.append(name)
    return stale


def main() -> None:
    if len(sys.argv) > 2:
        raise SystemExit("usage: resolve_lake_if_needed.py [checkout]")
    root = Path(sys.argv[1]) if len(sys.argv) == 2 else Path(__file__).resolve().parent.parent
    stale = stale_requires(root)
    if stale:
        print(f"Resolving changed latest-main requires: {', '.join(stale)}", flush=True)
        subprocess.run(["lake", "update", *stale], cwd=root, check=True)
    else:
        print("Own-organisation Lake requires already resolve to fetched main; skip update")


if __name__ == "__main__":
    main()
