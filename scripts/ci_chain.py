#!/usr/bin/env python3
"""Prepare own-organisation dependencies at latest main, preserving local work.

By default Lake refreshes the resolved manifest separately. Leaves are a non-Lean package,
so their checkout is prepared here even though Lake does not require them.

    ci_chain.py [checkout] [--record-resolved]

The optional record updates only existing own-organisation manifest revisions to
the actual resolved main checkouts. It creates no accepted input or seal record.
"""

import argparse
import json
import subprocess
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", nargs="?", type=Path,
                        default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--record-resolved", action="store_true",
                        help="record actual main SHAs for existing own-organisation manifest entries")
    args = parser.parse_args()
    root = args.checkout
    manifest_path = root / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    packages = root / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    entries = {}
    for entry in manifest["packages"]:
        name = entry["name"]
        # Lake prints identifiers containing punctuation with Lean's quotation marks.
        if name.startswith("«") and name.endswith("»"):
            name = name[1:-1]
        if name in CHAIN:
            entries[name] = entry
    if "cas_leaves" not in entries:
        entries["cas_leaves"] = {"url": "https://github.com/dzackgarza/lean-cas-dsl-leaves"}
    for name, entry in entries.items():
        sync_repository(packages / name, entry["url"])
    if args.record_resolved:
        for entry in manifest["packages"]:
            name = entry["name"]
            if name.startswith("«") and name.endswith("»"):
                name = name[1:-1]
            if name in entries:
                entry["rev"] = subprocess.check_output(
                    ["git", "-C", str(packages / name), "rev-parse", "HEAD"],
                    text=True).strip()
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
