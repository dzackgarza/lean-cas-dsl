#!/usr/bin/env python3
"""`lean-cas-dsl` ships no leaf (plan node gov-no-leaves-here).

The DSL consumes the leaves: it requires the leaf packages, and its permanent mathematical tests
and notebooks run here over whatever leaves are installed, passing or reporting gaps as leaves are
done. A leaf is written only in the leaf repository, in its own subtree, against the contract. So
this repository must contain no leaf code: no `register_leaf`, no tracked file under `CasLeaves/`.
A "probe" that registers a minimal leaf here is a leaf shipped in the DSL.

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
REGISTER = re.compile(r"^\s*register_leaf\b", re.MULTILINE)


def tracked(root: Path) -> list[str]:
    return subprocess.run(["git", "-C", str(root), "ls-files"], check=True, capture_output=True,
                          text=True).stdout.splitlines()


def violations(root: Path) -> list[str]:
    out = []
    for f in tracked(root):
        if f.startswith("CasLeaves/"):
            out.append(f"{f}: a leaf file in lean-cas-dsl")
        elif f.endswith(".lean"):
            text = (root / f).read_text()
            for m in REGISTER.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                out.append(f"{f}:{line}: registers a leaf (`register_leaf`) in lean-cas-dsl")
    return out


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        subprocess.run(["git", "-C", tmp, "init", "-q"], check=True)
        (root / "lakefile.lean").write_text("require cas_leaves from git\n")
        (root / "CasLeaves").mkdir()
        (root / "CasLeaves" / "X.lean").write_text("")
        (root / "A.lean").write_text("import CasContract.Leaf\nregister_leaf { backend := \"x\" }\n")
        (root / "B.lean").write_text("public import CasLeaves.Foo\n")
        subprocess.run(["git", "-C", tmp, "add", "."], check=True)
        found = violations(root)
        # Requiring and importing the leaf packages is the DSL consuming them: allowed.
        if len(found) != 2 or not any("CasLeaves/X.lean" in f for f in found) or \
                not any(f.startswith("A.lean:2:") for f in found):
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
        print("lean-cas-dsl ships no leaf; leaves are written in the leaf repository "
              "(gov-no-leaves-here):", file=sys.stderr)
        print("\n".join("  " + f for f in found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
