#!/usr/bin/env python3
"""An admitted assertion is protected as a question, not as text (gov-meaning-permanence).

    check_question_permanence.py --base BASE_RECORD REPORT
                                                   fail if the head's record drops or changes an entry
                                                   of the base's record (it is append-only), or if an
                                                   admitted assertion's semantic question differs from
                                                   the one recorded for it
    check_question_permanence.py --show REPORT     print each unrecorded assertion's proposition, as
                                                   the acceptance author reads it before recording

REPORT is the JSON report of `cas-harness --report`: per statement, its outcome and its `question`,
the fingerprint of the proposition the semantic reading elaborates (`Realize.claimQuestion`). The
record is `CasAcceptance/Permanent/questions.json`. The comparison is against the record of the
accepted revision (`--base`, the base checkout's file): a candidate that changes a reading and
rewrites the matching entry in the same change fails, because the base entry is kept.

A kernel, parser or pin under which an unchanged assertion elaborates to another proposition fails
here, whatever the outcome. The comparison is never by text, outcome or provability: an assertion
whose text changed is `check_acceptance_permanent.py`'s, and its new question is recorded only
with its correction. An assertion that the reading cannot read at all (no question) is reported,
and fails only if a question was recorded for it. Recording requires independent acceptance;
this checker exposes no mutation command.
runs only with `AGENT_ROLE=acceptance` (specs/architecture.md, "Authors: one role per agent").
"""

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "CasAcceptance" / "Permanent" / "questions.json"
INVENTORY = ROOT / "CasAcceptance" / "Permanent" / "admitted.json"


def questions(report: Path) -> dict[str, str]:
    results = json.loads(report.read_text())
    found: dict[str, str] = {}
    for result in results:
        ident = result["id"]
        if ident.startswith("(statement)"):
            continue
        if ident in found:
            raise SystemExit(f"duplicate assertion in report: {ident}")
        found[ident] = result["question"]
    return found


def main() -> int:
    args = sys.argv[1:]
    if args[:1] == ["--show"] and len(args) == 2:
        recorded = json.loads(RECORD.read_text()) if RECORD.is_file() else {}
        for r in json.loads(Path(args[1]).read_text()):
            if r["question"] and r["id"] not in recorded and not r["id"].startswith("(statement)"):
                print(f"{r['id']}: {r['proposition']}")
        return 0
    # Interpretation records require independently assessed input; a caller's
    # role environment cannot authorize new mathematical question identities.
    if args[:1] == ["--record"]:
        return 2
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
    if not INVENTORY.is_file():
        raise SystemExit(f"missing admitted assertion inventory: {INVENTORY}")
    inventory = set(json.loads(INVENTORY.read_text())["assertions"])
    head = questions(report)
    omitted = sorted(inventory - set(head))
    unexpected = sorted(set(head) - inventory)
    for ident in omitted:
        print(f"ADMITTED ASSERTION MISSING: {ident}")
    for ident in unexpected:
        print(f"UNADMITTED ASSERTION IN REPORT: {ident}")
    if omitted or unexpected:
        return 1
    unread = sorted(ident for ident in inventory if not head[ident])
    if unread:
        for ident in unread:
            print(f"ADMITTED QUESTION NOT READ: {ident}")
        return 1
    if not RECORD.is_file():
        raise SystemExit(f"missing candidate question record: {RECORD}")
    recorded = json.loads(RECORD.read_text())
    assert base_record is not None
    if not base_record.is_file():
        raise SystemExit(f"missing accepted question record: {base_record}")
    accepted = json.loads(base_record.read_text())
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
    return 1 if changed or missing or rewritten or unrecorded else 0


if __name__ == "__main__":
    sys.exit(main())
