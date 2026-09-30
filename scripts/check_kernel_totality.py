#!/usr/bin/env python3
"""The kernel never makes a term defined by catching its failure (LC-14; plan node
gov-kernel-lc14).

A statement is read once. A term outside an operation's domain is invalid when it is read. The
reading never tries one interpretation, catches the failure, and silently tries another: that
reinterprets a term until it lands in some domain (a divisor retried in another set, an element
re-read in its own set when it fails in `Y`). Every `catch` in the kernel (`CasCatalogue/`) must
therefore say, on its line or the line above, why it is not such a fallback:

    -- not a reading fallback: <reason>

for example a catch that records a computational failure as a stratum, or one that rethrows.
An unmarked `catch` fails the gate, with its file and line.

    check_kernel_totality.py              check the kernel
    check_kernel_totality.py --self-test  the gate refuses an unmarked catch and accepts a marked one
"""

from __future__ import annotations

import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KERNEL = "CasCatalogue"
CATCH = re.compile(r"\bcatch\b")
MARK = "-- not a reading fallback:"


def violations(root: Path) -> list[str]:
    out = []
    for path in sorted((root / KERNEL).rglob("*.lean")):
        lines = path.read_text().splitlines()
        for i, line in enumerate(lines):
            code = line.split("--", 1)[0]
            if not CATCH.search(code):
                continue
            if MARK in line or (i > 0 and MARK in lines[i - 1]):
                continue
            out.append(f"{path.relative_to(root)}:{i + 1}: unmarked `catch` (LC-14): "
                       f"{line.strip()}")
    return out


def self_test() -> int:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / KERNEL).mkdir()
        (root / KERNEL / "A.lean").write_text(
            "def f := try g catch _ => h\n"
            f"{MARK} a computational failure is recorded as a stratum\n"
            "def k := try g catch e => record e\n")
        found = violations(root)
        if len(found) != 1 or "A.lean:1:" not in found[0]:
            print(f"check_kernel_totality self-test failed: {found}", file=sys.stderr)
            return 1
    return 0


def main() -> int:
    if sys.argv[1:] == ["--self-test"]:
        return self_test()
    if sys.argv[1:]:
        raise SystemExit(__doc__)
    found = violations(ROOT)
    if found:
        print("the kernel never makes a term defined by catching its failure "
              "(lean-categories CONTRIBUTING LC-14):", file=sys.stderr)
        print("\n".join("  " + f for f in found), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
