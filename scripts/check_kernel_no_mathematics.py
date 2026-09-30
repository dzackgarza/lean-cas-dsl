#!/usr/bin/env python3
"""The kernel carries no mathematics (plan node gov-evidence-upstream).

`CasCatalogue/` (the kernel and the language) interprets the catalogue; it owns no mathematics,
and no proof automation about mathematics either. Whether a value lies in a domain (a unit, a
monic polynomial, a smooth map) and how that is established is the domain's, formalized in
`lean-categories` with the domain; the kernel runs what the catalogue registers and nothing else.
This gate fails, with file and line, when kernel code (comments and docstrings excluded):

* imports Mathlib outside `Mathlib.CategoryTheory` (the categorical infrastructure the kernel
  interprets the catalogue with);
* names mathematics: a mathematical namespace, lemma or domain tactic (`MATHEMATICS` below).

    check_kernel_no_mathematics.py              check the kernel
    check_kernel_no_mathematics.py --self-test  the gate refuses each case on a synthetic tree
"""

from __future__ import annotations

import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KERNEL = "CasCatalogue"
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(Mathlib\.\S+)", re.MULTILINE)
MATHEMATICS = re.compile(
    r"\b(Polynomial|Matrix|Real|Complex|IsUnit|isUnit_\w*|ContDiff|Continuous|"
    r"Monic|monicity!?|compute_degree!?|fun_prop|continuity|norm_num|positivity|linarith|"
    r"nlinarith|ring_nf|field_simp|Nat\.Prime|Finset|det_\w+)\b")


def code_lines(text: str) -> list[tuple[int, str]]:
    """The lines of `text` with comments and docstrings blanked, numbered from 1."""
    out, depth = [], 0
    for number, line in enumerate(text.splitlines(), 1):
        code, i = "", 0
        while i < len(line):
            if line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth and line.startswith("-/", i):
                depth -= 1
                i += 2
            elif not depth and line.startswith("--", i):
                break
            else:
                if not depth:
                    code += line[i]
                i += 1
        out.append((number, code))
    return out


def violations(root: Path) -> list[str]:
    out = []
    for path in sorted((root / KERNEL).rglob("*.lean")):
        text = path.read_text()
        rel = path.relative_to(root)
        for m in IMPORT.finditer(text):
            if not m.group(1).startswith("Mathlib.CategoryTheory"):
                line = text.count("\n", 0, m.start()) + 1
                out.append(f"{rel}:{line}: imports {m.group(1)}: mathematics is the catalogue's")
        for number, code in code_lines(text):
            if IMPORT.match(code):
                continue
            if m := MATHEMATICS.search(code):
                out.append(f"{rel}:{number}: names `{m.group(0)}`: {code.strip()[:90]}")
    return out


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / KERNEL).mkdir()
        (root / KERNEL / "A.lean").write_text(
            "public import Mathlib.CategoryTheory.Limits.Creates\n"
            "public import Mathlib.Analysis.SpecialFunctions.ExpDeriv\n"
            "/-- about `Real.exp` in a docstring -/\n"
            "def t := \"refine isUnit_iff_ne_zero.mpr ?_\"  -- `Matrix` in a comment\n")
        found = violations(root)
        if len(found) != 2 or not any("A.lean:2:" in f for f in found) or \
                not any("A.lean:4:" in f for f in found):
            print(f"check_kernel_no_mathematics self-test failed: {found}", file=sys.stderr)
            return 1
    return 0


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        raise SystemExit(__doc__)
    found = violations(ROOT)
    if found:
        print("the kernel carries no mathematics; a domain's evidence is formalized with the "
              "domain in lean-categories (gov-evidence-upstream):", file=sys.stderr)
        print("\n".join("  " + f for f in found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
