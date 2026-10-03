#!/usr/bin/env python3
"""Permanent acceptance assertions are append-only (specs/architecture.md, "Acceptance").

An admitted assertion is the text of an `#accept` command up to its `:=` (its id, provenance and
proposition; the proof after `:=` is how it is checked, and may change), or the whole text of an
`#accept_backend` command, in `CasAcceptance/Permanent/*.lean`, or a `test <id> "source": stmt`
item of the DSL suite `tests/acceptance/*.cas` together with the `let` items before it in its file,
with whitespace collapsed. Its hash is recorded in `CasAcceptance/Permanent/admitted.json`.

    check_acceptance_permanent.py
        Check the candidate against the retained admitted ledger.
    check_acceptance_permanent.py --base PATH
        Check the candidate against an independently selected accepted ledger.

This checker is read-only. It cannot admit, correct, or retire assertions, and a
caller-set role label grants no authority. The independent acceptance author proposes
ledger changes through the existing acceptance/review channel; only that independently
accepted transition advances the authoritative ledger. Candidate checks never do so.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DIR = ROOT / "CasAcceptance" / "Permanent"
MANIFEST = DIR / "admitted.json"
START = re.compile(r'^#accept(_backend)? "([^"]+)"')
SUITE = ROOT / "tests" / "acceptance"
TEST = re.compile(r'^test (\S+) "')


def assertions() -> dict[str, str]:
    found: dict[str, str] = {}
    for path in sorted(DIR.glob("*.lean")):
        lines = path.read_text().splitlines()
        i = 0
        while i < len(lines):
            m = START.match(lines[i])
            if not m:
                i += 1
                continue
            backend, ident = m.group(1), m.group(2)
            block = [lines[i]]
            i += 1
            while i < len(lines) and lines[i].strip() and (lines[i][0] in " \t"):
                block.append(lines[i])
                i += 1
            text = " ".join(" ".join(block).split())
            if not backend:
                if " := " not in text:
                    raise SystemExit(f"{path.name}: #accept {ident} has no ':='")
                text = text.split(" := ", 1)[0]
            if ident in found:
                raise SystemExit(f"{path.name}: the assertion {ident} is stated twice")
            found[ident] = hashlib.sha256(text.encode()).hexdigest()
    for path in sorted(SUITE.glob("*.cas")):
        lets: list[str] = []
        for item in re.split(r"\n\s*\n", path.read_text()):
            lines = [l for l in item.splitlines() if l.strip() and not l.lstrip().startswith("--")]
            if not lines:
                continue
            text = " ".join(" ".join(lines).split())
            m = TEST.match(text)
            if text.startswith("let "):
                lets.append(text)
            elif not m:
                raise SystemExit(f"{path.name}: an item is neither a test nor a let: {text}")
            else:
                ident = m.group(1)
                if ident in found:
                    raise SystemExit(f"{path.name}: the assertion {ident} is stated twice")
                found[ident] = hashlib.sha256(" ; ".join(lets + [text]).encode()).hexdigest()
    return found


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, default=MANIFEST,
                        help="accepted assertion ledger supplied by the evaluating operation")
    args = parser.parse_args()
    current = assertions()
    # A missing or malformed authoritative input fails the operation. It is never
    # reconstructed from whichever assertions the candidate happens to contain.
    manifest = json.loads(args.base.read_text())
    admitted: dict[str, str] = manifest["assertions"]
    missing = sorted(set(admitted) - set(current))
    changed = sorted(i for i in admitted if i in current and current[i] != admitted[i])
    new = sorted(set(current) - set(admitted))
    problems = [f"admitted assertion {i} was deleted" for i in missing]
    problems += [f"admitted assertion {i} was modified" for i in changed]
    problems += [f"assertion {i} has no independent admission" for i in new]
    if problems:
        print("permanent acceptance assertions are append-only:", file=sys.stderr)
        print("\n".join("  " + p for p in problems), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
