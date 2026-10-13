#!/usr/bin/env python3
"""`lean-cas-dsl` ships no leaf, and imports none (plan nodes gov-no-leaves-here,
gov-leaf-authority; specs/leaf-registration.md).

A leaf is a manifest of registrations (`leaves.json`) and the programs it names, in the leaf
repository; it ships no Lean, and the kernel imports nothing from it. The suite runs here over
whatever manifest is installed, found by path (`CAS_LEAVES`), never by a Lake dependency. So this
repository must contain no leaf and reach no leaf's code: no tracked file under `CasLeaves/`, no
`register_leaf` or its former functions (a leaf registration has no meaning here or anywhere), no
`import CasLeaves…` in any Lean module, and no `require cas_leaves` in `lakefile.lean`.
A "probe" that registers or imports a leaf here is a leaf shipped in the DSL.

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
REGISTER = re.compile(r"(^\s*register_leaf\b)|\b(registerLeaf|addLeafRegistryEntryChecked)\b", re.MULTILINE)
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?CasLeaves\b", re.MULTILINE)
REQUIRE = re.compile(r"^\s*require\s+cas_leaves\b", re.MULTILINE)


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
                out.append(f"{f}:{line}: registers a leaf in lean-cas-dsl")
            for m in IMPORT.finditer(text):
                line = text.count("\n", 0, m.start()) + 1
                out.append(f"{f}:{line}: imports a leaf's Lean; a leaf ships none")
            if f == "lakefile.lean":
                for m in REQUIRE.finditer(text):
                    line = text.count("\n", 0, m.start()) + 1
                    out.append(f"{f}:{line}: requires the leaves as a Lake dependency; the "
                               "kernel imports nothing from a leaf")
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
        (root / "C.lean").write_text("import CasContract.Registration\n")
        subprocess.run(["git", "-C", tmp, "add", "."], check=True)
        found = violations(root)
        expected = ("CasLeaves/X.lean", "A.lean:2:", "B.lean:1:", "lakefile.lean:1:")
        if len(found) != 4 or not all(any(e in f for f in found) for e in expected) or \
                any("C.lean" in f for f in found):
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
        print("lean-cas-dsl ships no leaf and imports none; leaves are manifests in the leaf "
              "repository (gov-no-leaves-here, specs/leaf-registration.md):", file=sys.stderr)
        print("\n".join("  " + f for f in found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
