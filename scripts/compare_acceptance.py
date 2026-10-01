#!/usr/bin/env python3
"""Compare two runs of the acceptance suite, assertion by assertion (B0 gate family C).

    compare_acceptance.py BASE.json HEAD.json

Each file is the report `cas-harness --report` writes: one result per test, with its file, id and
outcome kind. The comparison is by assertion identity, never by counts. The head fails when an
assertion of the base is missing from it, or when an assertion the base did not fail (it held, was
a gap, or its backend was unavailable) fails at the head. A failing assertion that changes kind is
reported, and fails nothing: it was failing already. Statements that are not tests (`let`s) are
compared through the tests that use them.
"""

import json
import sys
from pathlib import Path

FAILING = {"wrong", "malformed", "invalid", "ambiguous", "internal"}


def outcomes(path: Path) -> dict[tuple[str, str], str]:
    results = json.loads(path.read_text())
    return {(r["file"], r["id"]): r["kind"] for r in results
            if not r["id"].startswith("(statement)")}


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    base, head = outcomes(Path(sys.argv[1])), outcomes(Path(sys.argv[2]))
    missing = sorted(key for key in base if key not in head)
    regressed = sorted((key, base[key], head[key]) for key in base
                       if key in head and base[key] not in FAILING and head[key] in FAILING)
    lost = sorted((key, base[key], head[key]) for key in base
                  if key in head and base[key] == "holds" and head[key] != "holds"
                  and head[key] not in FAILING)
    gained = sorted((key, base[key], head[key]) for key in head
                    if head[key] == "holds" and base.get(key) != "holds")
    rekinded = sorted((key, base[key], head[key]) for key in base
                      if key in head and base[key] in FAILING and head[key] in FAILING
                      and base[key] != head[key])
    for title, rows in (("now holds", gained), ("failing, now of another kind", rekinded),
                        ("held, now not computed", lost)):
        for (file, id_), before, after in rows:
            print(f"{title}: {file}: {id_}: {before} -> {after}")
    for file, id_ in missing:
        print(f"MISSING at the head: {file}: {id_}")
    for (file, id_), before, after in regressed:
        print(f"FAILS at the head: {file}: {id_}: {before} -> {after}")
    failing = sorted(key for key, kind in head.items() if kind in FAILING)
    print(f"{len(head)} assertions at the head; failing: "
          f"{', '.join(id_ for _, id_ in failing) or 'none'}")
    return 1 if missing or regressed or lost else 0


if __name__ == "__main__":
    sys.exit(main())
