#!/usr/bin/env python3
"""An admitted assertion is protected as a question, not as text (gov-meaning-permanence).

    check_question_permanence.py REPORT            fail if an admitted assertion's semantic question
                                                   differs from the one recorded at admission
    check_question_permanence.py --record REPORT   record the question of every admitted assertion
                                                   that has none recorded; never changes a recorded one
    check_question_permanence.py --show REPORT     print each unrecorded assertion's proposition, as
                                                   the acceptance author reads it before recording

REPORT is the JSON report of `cas-harness --report`: per statement, its outcome and its `question`,
the fingerprint of the proposition the semantic reading elaborates (`Realize.claimQuestion`). The
record is `CasAcceptance/Permanent/questions.json`.

A kernel, parser or pin under which an unchanged assertion elaborates to another proposition fails
here, whatever the outcome. The comparison is never by text, outcome or provability: an assertion
whose text changed is `check_acceptance_permanent.py`'s, and its new question is recorded only
with its correction. An assertion that the reading cannot read at all (no question) is reported,
and fails only if a question was recorded for it. Recording is the acceptance author's: `--record`
runs only with `AGENT_ROLE=acceptance` (specs/architecture.md, "Authors: one role per agent").
"""

import json
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "CasAcceptance" / "Permanent" / "questions.json"


def questions(report: Path) -> dict[str, str]:
    results = json.loads(report.read_text())
    return {r["id"]: r["question"] for r in results
            if not r["id"].startswith("(statement)")}


def main() -> int:
    args = sys.argv[1:]
    if args[:1] == ["--show"] and len(args) == 2:
        recorded = json.loads(RECORD.read_text()) if RECORD.is_file() else {}
        for r in json.loads(Path(args[1]).read_text()):
            if r["question"] and r["id"] not in recorded and not r["id"].startswith("(statement)"):
                print(f"{r['id']}: {r['proposition']}")
        return 0
    record = args[:1] == ["--record"]
    if record:
        args = args[1:]
        if os.environ.get("AGENT_ROLE") != "acceptance":
            raise SystemExit("--record is the acceptance author's (AGENT_ROLE=acceptance)")
    if len(args) != 1:
        print(__doc__, file=sys.stderr)
        return 2
    report = Path(args[0])
    if not report.is_file():
        raise SystemExit(f"no report at {report}: the suite did not run to completion")
    head = questions(report)
    recorded = json.loads(RECORD.read_text()) if RECORD.is_file() else {}
    if record:
        added = {i: q for i, q in head.items() if q and i not in recorded}
        RECORD.write_text(json.dumps({**recorded, **added}, indent=1, sort_keys=True) + "\n")
        print(f"recorded {len(added)} questions; {len(recorded)} unchanged")
        return 0
    changed = sorted(i for i, q in recorded.items() if i in head and head[i] != q)
    missing = sorted(i for i in recorded if i not in head)
    for i in changed:
        print(f"QUESTION CHANGED: {i}: recorded {recorded[i]}, now {head[i] or '(not read)'}")
    for i in missing:
        print(f"QUESTION MISSING: {i} is recorded but not in the report")
    unrecorded = sorted(i for i, q in head.items() if q and i not in recorded)
    if unrecorded:
        print(f"{len(unrecorded)} assertions have no recorded question (the acceptance author records them)")
    print(f"{len(recorded)} recorded questions; {len(changed)} changed")
    return 1 if changed or missing else 0


if __name__ == "__main__":
    sys.exit(main())
