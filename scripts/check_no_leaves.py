#!/usr/bin/env python3
"""`lean-cas-dsl` neither depends on nor contains a leaf (plan node gov-no-leaves-here).

The language, the kernel and the permanent tests are written against the mathematics, blind to
every leaf (specs/architecture.md, "Authors: one role per agent"). All leaves live in the leaf
repository, probes included. This gate fails, with each location, when:

* the lakefile requires `cas_leaves`, or the lake manifest pins it;
* a tracked file lies under `CasLeaves/`;
* a tracked Lean module of this package imports a `CasLeaves` module.

    check_no_leaves.py              check this repository
    check_no_leaves.py --self-test  the gate refuses each case on a synthetic tree
"""

from __future__ import annotations

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*(public\s+)?(meta\s+)?import\s+CasLeaves\b", re.MULTILINE)


def tracked(root: Path) -> list[str]:
    return subprocess.run(["git", "-C", str(root), "ls-files"], check=True, capture_output=True,
                          text=True).stdout.splitlines()


def violations(root: Path) -> list[str]:
    out = []
    lakefile = root / "lakefile.lean"
    if lakefile.exists() and re.search(r"^\s*require\s+cas_leaves\b", lakefile.read_text(),
                                       re.MULTILINE):
        out.append("lakefile.lean requires cas_leaves")
    manifest = root / "lake-manifest.json"
    if manifest.exists() and '"name": "cas_leaves"' in manifest.read_text():
        out.append("lake-manifest.json pins cas_leaves")
    for f in tracked(root):
        if f.startswith("CasLeaves/"):
            out.append(f"{f}: a leaf file in lean-cas-dsl")
        elif f.endswith(".lean") and IMPORT.search((root / f).read_text()):
            out.append(f"{f}: imports a CasLeaves module")
    return out


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        subprocess.run(["git", "-C", tmp, "init", "-q"], check=True)
        (root / "lakefile.lean").write_text("require cas_leaves from git\n")
        (root / "CasLeaves").mkdir()
        (root / "CasLeaves" / "X.lean").write_text("")
        (root / "A.lean").write_text("public import CasLeaves.Foo\n")
        (root / "B.lean").write_text("import CasCatalogue\n")
        subprocess.run(["git", "-C", tmp, "add", "."], check=True)
        found = violations(root)
        expected = ["lakefile.lean requires cas_leaves", "CasLeaves/X.lean", "A.lean: imports"]
        if len(found) != 3 or not all(any(e in f for f in found) for e in expected):
            print(f"check_no_leaves self-test failed: {found}", file=sys.stderr)
            return 1
    return 0


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        raise SystemExit(__doc__)
    found = violations(ROOT)
    if found:
        print("lean-cas-dsl neither depends on nor contains a leaf (gov-no-leaves-here):",
              file=sys.stderr)
        print("\n".join("  " + f for f in found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
