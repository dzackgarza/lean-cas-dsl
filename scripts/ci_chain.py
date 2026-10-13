#!/usr/bin/env python3
"""Prepare own-organisation dependencies at latest main, preserving local work.

Lake refreshes the resolved manifest separately. Leaves are a non-Lean package,
so their checkout is prepared here even though Lake does not require them.

    ci_chain.py [checkout]        default: the checkout this script is in
"""

import json
import subprocess
import sys
from pathlib import Path

CHAIN = ("lean_categories", "cas_leaf_contracts", "cas_leaves", "nbdsl-worker")


def sync_repository(target: Path, url: str) -> None:
    if not target.exists():
        subprocess.run(["git", "clone", "--quiet", "--branch", "main", "--", url,
                        str(target)], check=True)
        return
    status = subprocess.check_output(
        ["git", "-C", str(target), "status", "--porcelain"], text=True)
    if status.strip():
        raise RuntimeError(f"{target}: uncommitted work; preserve it before updating main")
    actual_url = subprocess.check_output(
        ["git", "-C", str(target), "remote", "get-url", "origin"], text=True).strip()
    if actual_url != url:
        raise RuntimeError(f"{target}: origin {actual_url!r} differs from required {url!r}")
    subprocess.run(["git", "-C", str(target), "fetch", "--quiet", "origin",
                    "+refs/heads/main:refs/remotes/origin/main"], check=True)
    subprocess.run(["git", "-C", str(target), "switch", "--quiet", "--detach",
                    "refs/remotes/origin/main"], check=True)


def main() -> None:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = root / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    entries = {entry["name"]: entry for entry in manifest["packages"]
               if entry["name"] in CHAIN}
    if "cas_leaves" not in entries:
        entries["cas_leaves"] = {"url": "https://github.com/dzackgarza/lean-cas-dsl-leaves"}
    for name, entry in entries.items():
        sync_repository(packages / name, entry["url"])


if __name__ == "__main__":
    main()
