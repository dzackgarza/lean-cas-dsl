#!/usr/bin/env python3
"""Permanent acceptance assertions are append-only (specs/architecture.md, "Acceptance").

An admitted assertion is the text of an `#accept` command up to its `:=` (its id, provenance and
proposition; the proof after `:=` is how it is checked, and may change), or the whole text of an
`#accept_backend` command, in `CasAcceptance/Permanent/*.lean`, or a `test <id> "source": stmt`
item of the DSL suite `tests/acceptance/*.cas` together with the `let` items before it in its file,
with whitespace collapsed. Its hash is recorded in `CasAcceptance/Permanent/admitted.json`.

    check_acceptance_permanent.py           fail if an admitted assertion changed or disappeared,
                                            or an assertion is not admitted
    check_acceptance_permanent.py --admit   admit new assertions; never changes an admitted one
    check_acceptance_permanent.py --correct "reason"
                                            re-admit changed assertions after an upstream
                                            correction to the mathematics, recorded with the
                                            reason, which names the upstream commit

Admitting or correcting an assertion is the acceptance author's alone (specs/architecture.md,
"Authors: one role per agent"): `--correct` and `--admit` run only with `AGENT_ROLE=acceptance`.
A change to an admitted assertion or to the corrections also changes the sealed ledger, which only
an escalation accepts (custodian/CONTAINMENT.md).
"""

import hashlib
import os
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
    args = sys.argv[1:]
    current = assertions()
    manifest = (json.loads(MANIFEST.read_text()) if MANIFEST.exists()
                else {"assertions": {}, "corrections": []})
    admitted: dict[str, str] = manifest["assertions"]
    missing = sorted(set(admitted) - set(current))
    changed = sorted(i for i in admitted if i in current and current[i] != admitted[i])
    new = sorted(set(current) - set(admitted))

    def acceptance_author(action: str) -> None:
        if os.environ.get("AGENT_ROLE") != "acceptance":
            raise SystemExit(f"{action} is the acceptance author's (AGENT_ROLE=acceptance); an "
                             "implementation or orchestrator agent never admits or corrects the "
                             "tests that measure its work (specs/architecture.md, \"Authors: one "
                             "role per agent\")")

    if args[:1] == ["--correct"]:
        acceptance_author("--correct")
        if len(args) != 2 or not args[1].strip():
            raise SystemExit("--correct needs the upstream correction it records")
        for i in changed:
            admitted[i] = current[i]
        manifest["corrections"].append({"reason": args[1], "changed": changed, "removed": missing})
        for i in missing:
            del admitted[i]
        MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        return 0

    problems = [f"admitted assertion {i} was deleted" for i in missing]
    problems += [f"admitted assertion {i} was modified" for i in changed]
    if args == ["--admit"]:
        if new:
            acceptance_author(f"admitting {', '.join(new)}")
        if problems:
            print("\n".join(problems), file=sys.stderr)
            return 1
        for i in new:
            admitted[i] = current[i]
        MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        return 0
    if args:
        raise SystemExit(__doc__)
    problems += [f"assertion {i} is not admitted (run with --admit)" for i in new]
    if problems:
        print("permanent acceptance assertions are append-only:", file=sys.stderr)
        print("\n".join("  " + p for p in problems), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
