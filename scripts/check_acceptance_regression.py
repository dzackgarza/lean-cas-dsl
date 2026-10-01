#!/usr/bin/env python3
"""Compare two runs of the acceptance suite, assertion by assertion (B0 gate family C).

    check_acceptance_regression.py BASE.json HEAD.json

Each file is the report `cas-harness --report` writes: one result per test, with its file, id and
outcome kind. The comparison is by assertion identity, never by counts. The head fails when:
- an assertion of the base is missing from it;
- an assertion the base did not fail (it held, was a gap, or its backend was unavailable) fails at
  the head, or one that held is no longer computed;
- an assertion that is not in the base fails at the head: a new assertion is held to the suite,
  not to the base.
A statement that is not a test (a `let`) and does not hold is reported under its own text, and is
compared like a test. A failing assertion that changes kind is reported, and fails nothing: it was
failing already, and stays a failure to repair (stage A judges regression, not completion).

`cas-harness` writes its report only after the whole suite ran, so a run that did not complete
(a file that does not parse, a crash) leaves no report, and the comparison fails on it.
"""

import json
import sys
from pathlib import Path

FAILING = {"wrong", "malformed", "invalid", "ambiguous", "internal"}


def outcomes(path: Path) -> dict[tuple[str, str], str]:
    if not path.is_file():
        sys.exit(f"no report at {path}: the suite did not run to completion")
    results = json.loads(path.read_text())
    return {(r["file"], r["id"]): r["kind"] for r in results}


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
    new_failing = sorted((key, head[key]) for key in head
                         if key not in base and head[key] in FAILING)
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
    for (file, id_), after in new_failing:
        print(f"NEW and FAILS at the head: {file}: {id_}: {after}")
    failing = sorted(key for key, kind in head.items() if kind in FAILING)
    print(f"{len(head)} assertions at the head; failing: "
          f"{', '.join(id_ for _, id_ in failing) or 'none'}")
    return 1 if missing or regressed or lost or new_failing else 0


if __name__ == "__main__":
    sys.exit(main())
