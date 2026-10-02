#!/usr/bin/env python3
"""Compare every admitted question against independently accepted interpretations.

Usage: check_question_permanence.py --base BASE_RECORD REPORT
BASE_RECORD must be accompanied by admitted.json from the same accepted revision.
Candidate reports never create or amend accepted interpretations.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "CasAcceptance/Permanent/questions.json"
INVENTORY = ROOT / "CasAcceptance/Permanent/admitted.json"


def questions(report: Path) -> dict[str, str]:
    results = json.loads(report.read_text())
    out = {}
    for row in results:
        identity = row["id"]
        if identity.startswith("(statement)"):
            continue
        if identity in out:
            raise ValueError(f"duplicate assertion result: {identity}")
        out[identity] = row.get("question", "")
    return out


def main() -> int:
    args = sys.argv[1:]
    if len(args) != 3 or args[0] != "--base":
        print(__doc__, file=sys.stderr)
        return 2
    base, report = map(Path, args[1:])
    if not base.is_file() or not report.is_file() or not RECORD.is_file():
        print("missing accepted record or completed report", file=sys.stderr)
        return 1
    inventory_path = base.parent / "admitted.json"
    if not inventory_path.is_file():
        print("missing accepted assertion inventory", file=sys.stderr)
        return 1
    try:
        head = questions(report)
        accepted = json.loads(base.read_text())
        recorded = json.loads(RECORD.read_text())
        inventory = set(json.loads(inventory_path.read_text())["assertions"])
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"invalid question evidence: {error}", file=sys.stderr)
        return 1
    defects = []
    for identity, question in accepted.items():
        if recorded.get(identity) != question:
            defects.append(f"RECORD REWRITTEN: {identity}")
    for identity in sorted(inventory):
        if identity not in head:
            defects.append(f"QUESTION MISSING: {identity}")
        elif not head[identity]:
            defects.append(f"QUESTION NOT READ: {identity}")
        if not accepted.get(identity):
            defects.append(f"NO INDEPENDENTLY ACCEPTED INTERPRETATION: {identity}")
        elif identity in head and head[identity] != accepted[identity]:
            defects.append(f"QUESTION CHANGED: {identity}")
    for identity in sorted(set(head) - inventory):
        defects.append(f"UNADMITTED ASSERTION RESULT: {identity}")
    for defect in defects:
        print(defect)
    print(f"{len(inventory)} admitted assertions; {len(defects)} question defects")
    return int(bool(defects))


if __name__ == "__main__":
    sys.exit(main())
