#!/usr/bin/env python3
"""Pin this workspace's dependencies to the committed HEADs of their development checkouts.

`.lake/packages/{lean_categories,cas_leaf_contracts,cas_leaves}` are symbolic links to working
trees. Lake checks out the revision the root manifest pins inside them, so a dependency's work must
be committed and pinned here before this workspace builds, or the checkout discards it. This script
sets each package's revision, in `lakefile.lean` and `lake-manifest.json` of this repository and of
the dependent packages (the contract pins `lean_categories`; the leaves pin both), to the HEAD of
its checkout. It refuses a checkout with uncommitted changes.

    scripts/pin_dev.py            pin, and report what changed
"""

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PACKAGES = ["lean_categories", "cas_leaf_contracts", "cas_leaves"]
# Which packages each repository pins.
PINS = {
    ROOT: PACKAGES,
    ROOT / ".lake/packages/cas_leaf_contracts": ["lean_categories"],
    ROOT / ".lake/packages/cas_leaves": ["lean_categories", "cas_leaf_contracts"],
}


def head(package: str) -> str:
    path = (ROOT / ".lake/packages" / package).resolve()
    status = subprocess.run(["git", "-C", str(path), "status", "--porcelain"],
                            capture_output=True, text=True, check=True).stdout
    # Its own pin files may be pending: this script writes them (scripts/repin.sh commits them).
    dirty = [l for l in status.splitlines()
             if l[3:] not in ("lakefile.lean", "lake-manifest.json")]
    if dirty:
        raise SystemExit(f"{package} ({path}) has uncommitted changes: commit them first")
    return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                          capture_output=True, text=True, check=True).stdout.strip()


def main() -> int:
    heads = {p: head(p) for p in PACKAGES}
    for repo, packages in PINS.items():
        repo = repo.resolve()
        lakefile = repo / "lakefile.lean"
        manifest = repo / "lake-manifest.json"
        text = lakefile.read_text()
        data = json.loads(manifest.read_text())
        for package in packages:
            rev = heads[package]
            text = re.sub(rf'(require {package} from git\s*\n\s*"[^"]+" @ ")[0-9a-f]+(")',
                          rf"\g<1>{rev}\g<2>", text)
            for entry in data["packages"]:
                if entry["name"] == package:
                    entry["rev"] = rev
                    entry["inputRev"] = rev
        lakefile.write_text(text)
        manifest.write_text(json.dumps(data, indent=1) + "\n")
        print(f"{repo.name}: " + ", ".join(f"{p} {heads[p][:7]}" for p in packages))
    return 0


if __name__ == "__main__":
    sys.exit(main())
