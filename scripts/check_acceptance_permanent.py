#!/usr/bin/env python3
"""Permanent acceptance assertions are append-only (specs/architecture.md, "Acceptance").

An admitted assertion is the text of an `#accept` command up to its `:=` (its id, provenance and
proposition; the proof after `:=` is how it is checked, and may change), or the whole text of an
`#accept_backend` command, in `CasAcceptance/Permanent/*.lean`, with whitespace collapsed. Its
hash is recorded in `CasAcceptance/Permanent/admitted.json`.

    check_acceptance_permanent.py           fail if an admitted assertion changed or disappeared,
                                            or an assertion is not admitted
    check_acceptance_permanent.py --admit   admit new assertions; never changes an admitted one
    check_acceptance_permanent.py --correct "reason"
                                            re-admit changed assertions after an upstream
                                            correction to the mathematics: only when the pinned
                                            lean-categories revision differs from the one the
                                            manifest records, and recorded with the reason
"""

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DIR = ROOT / "CasAcceptance" / "Permanent"
MANIFEST = DIR / "admitted.json"
START = re.compile(r'^#accept(_backend)? "([^"]+)"')


def pin() -> str:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        if package["name"] == "lean_categories":
            return package["rev"]
    raise SystemExit("lake-manifest.json pins no lean_categories")


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
    return found


def main() -> int:
    args = sys.argv[1:]
    current = assertions()
    manifest = (json.loads(MANIFEST.read_text()) if MANIFEST.exists()
                else {"lean_categories": pin(), "assertions": {}, "corrections": []})
    admitted: dict[str, str] = manifest["assertions"]
    missing = sorted(set(admitted) - set(current))
    changed = sorted(i for i in admitted if i in current and current[i] != admitted[i])
    new = sorted(set(current) - set(admitted))

    if args[:1] == ["--correct"]:
        if len(args) != 2 or not args[1].strip():
            raise SystemExit("--correct needs the upstream correction it records")
        if pin() == manifest["lean_categories"]:
            raise SystemExit("an admitted assertion changes only with an upstream correction: "
                             "lean-categories is still pinned at the admitted revision")
        for i in changed:
            admitted[i] = current[i]
        manifest["corrections"].append({"lean_categories": pin(), "reason": args[1],
                                        "changed": changed, "removed": missing})
        for i in missing:
            del admitted[i]
        manifest["lean_categories"] = pin()
        MANIFEST.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        return 0

    problems = [f"admitted assertion {i} was deleted" for i in missing]
    problems += [f"admitted assertion {i} was modified" for i in changed]
    if args == ["--admit"]:
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
