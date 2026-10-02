#!/usr/bin/env python3
"""An admitted assertion is protected as a question, not as text (gov-meaning-permanence).

    check_question_permanence.py --base BASE_RECORD REPORT
                                                   fail if the head's record drops or changes an entry
                                                   of the base's record (it is append-only), or if an
                                                   admitted assertion's semantic question differs from
                                                   the one recorded for it
    check_question_permanence.py --record REPORT   record the question of every admitted assertion
                                                   that has none recorded; never changes a recorded one
    check_question_permanence.py --show REPORT     print each unrecorded assertion's proposition, as
                                                   the acceptance author reads it before recording
    check_question_permanence.py --transition ID REASON REPORT
                                                   accept a genuine change of ID's question: record the
                                                   transition from its recorded question to the one in
                                                   REPORT, with the reading that justifies it

REPORT is the JSON report of `cas-harness --report`: per statement, its outcome and its `question`,
the fingerprint of the proposition the semantic reading elaborates (`Realize.claimQuestion`). The
record is `CasAcceptance/Permanent/questions.json`. The comparison is against the record of the
accepted revision (`--base`, the base checkout's file): a candidate that changes a reading and
rewrites the matching entry in the same change fails, because the base entry is kept.

A genuine change of an assertion's question (a new reading of the same statement) needs independent
acceptance: the acceptance author reads the new proposition and records a transition
(`--transition`, `AGENT_ROLE=acceptance`) in `CasAcceptance/Permanent/question_transitions.json`,
from the recorded question to the new one, with the reason. The accepted question of an assertion is
its base entry carried along its transitions; the transitions are append-only like the record, so a
candidate cannot remove one or rewrite one, and an unrecorded change still fails.

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
TRANSITIONS = ROOT / "CasAcceptance" / "Permanent" / "question_transitions.json"


def load(path: Path) -> dict:
    """A JSON object file, or the empty object when the file does not exist (a record before its
    first entry)."""
    return json.loads(path.read_text()) if path.is_file() else {}


def carried(question: str, steps: list[dict]) -> str:
    """The question reached from `question` along its recorded transitions, in order."""
    for step in steps:
        if step["from"] == question:
            question = step["to"]
    return question


def questions(report: Path) -> dict[str, str]:
    results = json.loads(report.read_text())
    return {r["id"]: r["question"] for r in results
            if not r["id"].startswith("(statement)")}


def main() -> int:
    args = sys.argv[1:]
    if args[:1] == ["--show"] and len(args) == 2:
        recorded = load(RECORD)
        for r in json.loads(Path(args[1]).read_text()):
            if r["question"] and r["id"] not in recorded and not r["id"].startswith("(statement)"):
                print(f"{r['id']}: {r['proposition']}")
        return 0
    if args[:1] == ["--transition"]:
        if os.environ.get("AGENT_ROLE") != "acceptance":
            raise SystemExit("--transition is the acceptance author's (AGENT_ROLE=acceptance)")
        if len(args) != 4:
            print(__doc__, file=sys.stderr)
            return 2
        ident, reason, report = args[1], args[2], Path(args[3])
        head = questions(report)
        recorded, transitions = load(RECORD), load(TRANSITIONS)
        if ident not in recorded:
            raise SystemExit(f"{ident} has no recorded question to change")
        if ident not in head or not head[ident]:
            raise SystemExit(f"{ident} has no question in {report}")
        if head[ident] == recorded[ident]:
            raise SystemExit(f"{ident}'s question is unchanged")
        steps = transitions[ident] if ident in transitions else []
        transitions[ident] = steps + [{"from": recorded[ident], "to": head[ident], "reason": reason}]
        recorded[ident] = head[ident]
        TRANSITIONS.write_text(json.dumps(transitions, indent=1, sort_keys=True) + "\n")
        RECORD.write_text(json.dumps(recorded, indent=1, sort_keys=True) + "\n")
        print(f"{ident}: transition recorded")
        return 0
    record = args[:1] == ["--record"]
    if record:
        args = args[1:]
        if os.environ.get("AGENT_ROLE") != "acceptance":
            raise SystemExit("--record is the acceptance author's (AGENT_ROLE=acceptance)")
    base_record: Path | None = None
    if not record:
        if len(args) != 3 or args[0] != "--base":
            print(__doc__, file=sys.stderr)
            return 2
        base_record = Path(args[1])
        args = args[2:]
    if len(args) != 1:
        print(__doc__, file=sys.stderr)
        return 2
    report = Path(args[0])
    if not report.is_file():
        raise SystemExit(f"no report at {report}: the suite did not run to completion")
    head = questions(report)
    recorded = load(RECORD)
    if record:
        added = {i: q for i, q in head.items() if q and i not in recorded}
        RECORD.write_text(json.dumps({**recorded, **added}, indent=1, sort_keys=True) + "\n")
        print(f"recorded {len(added)} questions; {len(recorded)} unchanged")
        return 0
    assert base_record is not None
    # The base's transitions sit beside its record; the head's must extend them.
    base_transitions = load(base_record.parent / TRANSITIONS.name)
    transitions = load(TRANSITIONS)
    dropped = sorted(i for i, steps in base_transitions.items()
                     if i not in transitions or transitions[i][:len(steps)] != steps)
    for i in dropped:
        print(f"TRANSITION REWRITTEN: {i}: the base's transitions are not kept")
    # The accepted question: the base's entry carried along every recorded transition.
    accepted = {i: carried(q, transitions[i] if i in transitions else [])
                for i, q in load(base_record).items()}
    rewritten = sorted(i for i, q in accepted.items() if i not in recorded or recorded[i] != q)
    for i in rewritten:
        now = recorded[i] if i in recorded else "(removed)"
        print(f"RECORD REWRITTEN: {i}: accepted {accepted[i]}, head record {now}")
    recorded = {**recorded, **accepted}
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
    return 1 if changed or missing or rewritten or dropped else 0


if __name__ == "__main__":
    sys.exit(main())
