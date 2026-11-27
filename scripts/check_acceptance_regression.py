#!/usr/bin/env python3
"""Compare two runs of the acceptance suite, assertion by assertion (B0 gate family C).

    check_acceptance_regression.py BASE.json HEAD.json

Each file is the report `cas-harness --report` writes: one result per test, with its file, id and
outcome kind, optional stratum and explicit failure flag. Missing additive fields retain
legacy behavior. The comparison is by assertion identity, never by counts. The head fails when:
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
from typing import NamedTuple
from pathlib import Path

FAILING = {"wrong", "malformed", "invalid", "ambiguous", "internal"}
KINDS = {"holds", "gap", "unavailable"} | FAILING


class ReportOutcome(NamedTuple):
    kind: str
    stratum: str | None
    fails: bool

    def describe(self) -> str:
        details = [self.stratum] if self.stratum is not None else []
        if self.fails and self.kind not in FAILING:
            details.append("fails")
        return self.kind + (" [" + ", ".join(details) + "]" if details else "")


def report_outcome(result: dict) -> ReportOutcome:
    kind = result["kind"]
    stratum = result.get("stratum")
    explicit = result.get("fails", False)
    if kind not in KINDS or not isinstance(explicit, bool):
        raise ValueError("unknown outcome kind or invalid failure column")
    if stratum is not None and not isinstance(stratum, str):
        raise ValueError("an outcome stratum must be a string or null")
    # Old reports retain their original kind-based behavior. A false/missing flag
    # cannot erase a precise unread-source failure in an additive report.
    return ReportOutcome(kind, stratum,
                         explicit or kind in FAILING or stratum == "unsupportedSource")


def outcomes(path: Path) -> dict[tuple[str, str], ReportOutcome]:
    if not path.is_file():
        sys.exit(f"no report at {path}: the suite did not run to completion")
    results = json.loads(path.read_text())
    if not isinstance(results, list):
        raise ValueError("the suite report must be an array")
    found: dict[tuple[str, str], ReportOutcome] = {}
    for result in results:
        key = (result["file"], result["id"])
        if not all(isinstance(part, str) for part in key):
            raise ValueError("a report row lost its file or assertion identity")
        if key in found:
            sys.exit(f"duplicate assertion in report {path}: {key}")
        found[key] = report_outcome(result)
    return found


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    base, head = outcomes(Path(sys.argv[1])), outcomes(Path(sys.argv[2]))
    # A failing statement (a `let`) is reported only while it fails: absent at the head, it holds.
    missing = sorted(key for key in base if key not in head and not key[1].startswith("(statement)"))
    resolved = sorted(key for key in base if key not in head and key[1].startswith("(statement)"))
    regressed = sorted((key, base[key], head[key]) for key in base
                       if key in head and not base[key].fails and head[key].fails)
    lost = sorted((key, base[key], head[key]) for key in base
                  if key in head and base[key].kind == "holds" and head[key].kind != "holds"
                  and not head[key].fails)
    new_failing = sorted((key, head[key]) for key in head
                         if key not in base and head[key].fails)
    gained = sorted((key, base[key] if key in base else None, head[key]) for key in head
                    if head[key].kind == "holds" and not head[key].fails
                    and (key not in base or base[key].kind != "holds" or base[key].fails))
    rekinded = sorted((key, base[key], head[key]) for key in base
                      if key in head and base[key].fails and head[key].fails
                      and base[key] != head[key])
    for title, rows in (("now holds", gained), ("failing, now of another kind", rekinded),
                        ("held, now not computed", lost)):
        for (file, id_), before, after in rows:
            previous = before.describe() if before is not None else "not previously observed"
            print(f"{title}: {file}: {id_}: {previous} -> {after.describe()}")
    for file, id_ in resolved:
        print(f"statement now holds: {file}: {id_}")
    for file, id_ in missing:
        print(f"MISSING at the head: {file}: {id_}")
    for (file, id_), before, after in regressed:
        print(f"FAILS at the head: {file}: {id_}: {before.describe()} -> {after.describe()}")
    for (file, id_), after in new_failing:
        print(f"NEW and FAILS at the head: {file}: {id_}: {after.describe()}")
    failing = sorted(key for key, outcome in head.items() if outcome.fails)
    print(f"{len(head)} assertions at the head; failing: "
          f"{', '.join(id_ for _, id_ in failing) or 'none'}")
    return 1 if missing or regressed or lost or new_failing else 0


if __name__ == "__main__":
    sys.exit(main())
