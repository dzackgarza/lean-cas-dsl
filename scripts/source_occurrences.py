"""Reconcile native source inventories with current execution evidence."""
from __future__ import annotations

from collections import defaultdict
from decimal import Decimal
import hashlib
import math


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _span(value: object, file: str, source: bytes) -> tuple[int, int]:
    _require(isinstance(value, dict) and value.get("file") == file,
             "source span changed its original file")
    start, stop = value.get("startByte"), value.get("stopByte")
    _require(type(start) is int and type(stop) is int and 0 <= start < stop <= len(source),
             "source span is outside the original input")
    _require(all(offset == len(source) or source[offset] & 0xC0 != 0x80
                 for offset in (start, stop)), "source span splits a UTF-8 character")
    return start, stop


def _outcome(data: dict) -> dict:
    _require(isinstance(data.get("kind"), str) and bool(data["kind"])
             and (data.get("stratum") is None or isinstance(data["stratum"], str))
             and isinstance(data.get("detail"), str) and type(data.get("fails")) is bool,
             "terminal event lost its actual outcome")
    return {field: data.get(field) for field in ("kind", "stratum", "detail", "fails")}


def _timing(event: dict) -> dict:
    data = event["data"]
    result = {}
    for native, public in (("milliseconds", "milliseconds"),
                           ("executionMilliseconds", "execution_milliseconds"),
                           ("setupMilliseconds", "setup_milliseconds")):
        if native not in data and native != "milliseconds":
            continue
        value = data.get(native)
        _require(type(value) in (int, float, Decimal), "missing native execution timing")
        finite = value.is_finite() if isinstance(value, Decimal) else (
            math.isfinite(value) if isinstance(value, float) else True)
        _require(finite and value >= 0, "invalid native execution timing")
        result[public] = value
    return result


def _reconcile_file(report: dict, record: dict, rows: list[dict], stops: list[dict]) -> set:
    errors = report["errors"]
    start, finish, failure = record.get("start"), record.get("completion"), record.get("failure")
    if start is None and failure is not None:
        _require(finish is None and not rows, "failed file also claims parsed execution")
        report["failure"] = failure["data"]
        report["status"] = "unparsed"
        report["source_sha256"] = failure["data"].get("sourceSha256")
        report["compact"] = failure["data"].get("compact")
        _require(isinstance(report["compact"], list), "failed file lost its exact compact outcome")
        return set()
    _require(start is not None, "file has no pre-execution native source inventory")
    data = start["data"]
    file, session, file_run = report["file"], report["session"], report["file_run"]
    _require(start["session"] == session and data["file"] == file and data["fileRun"] == file_run,
             "native inventory changed its file identity")
    text, inventory = data.get("sourceText"), data.get("inventory")
    _require(isinstance(text, str) and isinstance(inventory, list),
             "file has no original source text and ordered native inventory")
    source = text.encode("utf-8")
    source_hash = hashlib.sha256(source).hexdigest()
    _require(source_hash == data["sourceSha256"], "native source inventory hash does not match its input")
    report["source_sha256"] = source_hash
    if finish is None:
        errors.append("file has no native completion and compact projection")
    else:
        _require(finish["session"] == session and all(finish["data"][field] == data[field]
                 for field in ("file", "fileRun", "sourceSha256")),
                 "file completion changed its original input")
        _require(isinstance(finish["data"].get("compact"), list),
                 "file completion lost the exact compact projection")
        report["compact"] = finish["data"]["compact"]

    nodes, siblings, spans = {}, defaultdict(list), {}
    for item in inventory:
        _require(isinstance(item, dict), "invalid native source inventory entry")
        path = item.get("path")
        _require(isinstance(path, list) and bool(path)
                 and all(type(index) is int and index >= 0 for index in path),
                 "invalid source occurrence path")
        key, parent = tuple(path), tuple(path[:-1])
        _require(key not in nodes, "duplicate source occurrence path")
        _require(_same(item.get("parent"), list(parent) if parent else None)
                 and type(item.get("ordinal")) is int and item["ordinal"] == path[-1]
                 and path[-1] == len(siblings[parent]), "source occurrence lost its sibling ordinal or parent")
        _require(not parent or parent in nodes and nodes[parent]["isScope"],
                 "source occurrence has no preceding scope parent")
        _require(isinstance(item.get("syntaxKind"), str) and bool(item["syntaxKind"])
                 and isinstance(item.get("source"), str) and type(item.get("isScope")) is bool
                 and (item.get("id") is None or isinstance(item["id"], str) and bool(item["id"])),
                 "invalid native source occurrence description")
        bounds = _span(item.get("position"), file, source)
        execution = _span(item.get("executionPosition"), file, source)
        _require(bounds[0] <= execution[0] < execution[1] <= bounds[1],
                 "execution span is outside its original source occurrence")
        if parent:
            enclosing = _span(nodes[parent]["executionPosition"], file, source)
            _require(enclosing[0] <= bounds[0] < bounds[1] <= enclosing[1],
                     "source occurrence escaped its native parent span")
            _require(execution == bounds, "nested execution lost its full cas_item span")
        if siblings[parent]:
            _require(spans[siblings[parent][-1]][1] <= bounds[0], "source siblings overlap or changed order")
        nodes[key], spans[key] = item, bounds
        siblings[parent].append(key)
    _require(list(nodes) == sorted(nodes), "native source inventory is not in preorder")
    _require(len(siblings[()]) == data["statements"], "native source inventory lost a root statement")

    roots, children = defaultdict(list), defaultdict(list)
    for row in rows:
        _require(row.get("file") == file and row.get("input_sha256") == source_hash,
                 "computation changed its original source input")
        if row["unit"] == "statement":
            roots[row["ordinal"]].append(row)
        else:
            _require(row["unit"] == "nested_statement", "unknown file computation unit")
            children[(row.get("parent_computation"), row["ordinal"])].append(row)
    actual, by_start, used = {}, {}, set()
    for path, item in nodes.items():
        parent_row = actual.get(path[:-1])
        matches = (roots[item["ordinal"]] if len(path) == 1 else
                   children[(parent_row["computation"], item["ordinal"])] if parent_row else [])
        if len(matches) > 1:
            errors.append(f"{list(path)}: duplicate native computation")
        if not matches:
            continue
        row = matches[0]
        actual[path] = row
        used.add(id(row))
        begun = row.get("start")
        if begun is None:
            errors.append(f"{list(path)}: native computation lost its start")
            continue
        expected_id = item["id"] if item["id"] is not None else "(statement) " + item["source"]
        _require(begun["session"] == session and _same(begun["data"].get("position"), item["executionPosition"])
                 and begun["data"].get("ordinal") == item["ordinal"]
                 and begun["data"].get("id") == expected_id,
                 f"{list(path)}: native start does not identify its source occurrence")
        if len(path) == 1:
            _require(begun["parents"] == start["parents"] and begun["sequence"] > start["sequence"],
                     f"{list(path)}: computation does not follow its owning source inventory")
        else:
            _require(begun["data"].get("source") == item["source"],
                     f"{list(path)}: nested computation changed its original source")
            owner = parent_row["start"]
            ancestry = owner["parents"] + [owner["sequence"]]
            _require(begun["parents"][:len(ancestry)] == ancestry,
                     f"{list(path)}: nested computation lost its native causal parent")
        _require(begun["sequence"] not in by_start, "duplicate native computation start")
        by_start[begun["sequence"]] = path
        terminal = row.get("completion") or row.get("interruption")
        if terminal is not None:
            _require(terminal["session"] == session and terminal["parents"] ==
                     begun["parents"] + [begun["sequence"]]
                     and terminal["sequence"] > begun["sequence"],
                     f"{list(path)}: terminal event lost its actual start")
            _require(finish is None or terminal["sequence"] < finish["sequence"],
                     f"{list(path)}: computation ended after its file completed")
        if row.get("complete") is not True:
            errors.append(f"{list(path)}: native computation timing is incomplete")
    if any(id(row) not in used for row in rows):
        errors.append("file contains computations outside its native source inventory")

    skipped, stopped, claimed = {}, set(), set()
    for stop in stops:
        if stop.get("session") != session:
            continue
        owner = next((by_start[parent] for parent in reversed(stop.get("parents", []))
                      if parent in by_start), None)
        if owner is None:
            continue
        claimed.add((session, stop["sequence"]))
        _require(nodes[owner]["isScope"] and owner not in stopped,
                 "scope stop has no unique source scope")
        stopped.add(owner)
        owner_start = actual[owner]["start"]
        ancestry = owner_start["parents"] + [owner_start["sequence"]]
        _require(stop["parents"][:len(ancestry)] == ancestry,
                 "scope stop lost its native causal parent")
        stopped_data = stop["data"]
        _require(type(stopped_data.get("failedChild")) is int, "invalid failed child identity")
        failed = by_start.get(stopped_data["failedChild"])
        _require(failed is not None and failed[:-1] == owner
                 and type(stopped_data.get("failedOrdinal")) is int
                 and failed[-1] == stopped_data["failedOrdinal"],
                 "scope stop lost its actual failed child")
        failed_finish = actual[failed].get("completion")
        _require(failed_finish is not None and failed_finish["data"].get("kind") != "holds"
                 and failed_finish["sequence"] < stop["sequence"],
                 "scope stop has no preceding non-holding child outcome")
        owner_finish = actual[owner].get("completion")
        _require(owner_finish is None or stop["sequence"] < owner_finish["sequence"],
                 "scope stopped after its own completion")
        tail = siblings[owner][failed[-1] + 1:]
        _require(_same(stopped_data.get("skipped"), [
            {"ordinal": nodes[path]["ordinal"], "position": nodes[path]["position"]} for path in tail]),
            "scope stop changed the exact unexecuted source tail")
        for root in tail:
            for path in nodes:
                if path[:len(root)] == root:
                    _require(path not in actual and path not in skipped,
                             "scope stop contradicts an actual or previously skipped occurrence")
                    skipped[path] = stop

    for path, item in nodes.items():
        row = actual.get(path)
        root = actual.get(path[:1])
        root_finish = root.get("completion") if root else None
        root_outcome = root_finish["data"].get("result") if root_finish else None
        enclosing = root_outcome.get("published") if isinstance(root_outcome, dict) else None
        _require(enclosing is None or type(enclosing) is bool, "invalid enclosing publication decision")
        observed = {
            "path": list(path), "parent": list(path[:-1]) if len(path) > 1 else None,
            "ordinal": item["ordinal"], "syntax_kind": item["syntaxKind"], "id": item["id"],
            "source": item["source"], "source_span": item["position"],
            "execution_span": item["executionPosition"], "is_scope": item["isScope"],
            "status": "incomplete", "attempted": None, "outcome": None, "staged": None,
            "enclosing_published": enclosing, "published": None,
            "eventrefs": {"start": None, "terminal": None, "timing": None, "scope_stop": None,
                          "enclosing_timing": root_finish["sequence"] if root_finish else None},
            "timing": None,
        }
        report["occurrences"].append(observed)
        if row is not None:
            begun = row.get("start")
            terminal = row.get("completion") or row.get("interruption")
            observed["eventrefs"]["start"] = begun["sequence"] if begun else None
            if terminal is not None:
                observed["eventrefs"]["terminal"] = terminal["sequence"]
                observed["eventrefs"]["timing"] = terminal["sequence"]
                observed["timing"] = _timing(terminal)
            completion = row.get("completion")
            if completion is None:
                errors.append(f"{list(path)}: attempted occurrence has no native terminal timing")
                continue
            outcome = completion["data"].get("result") if len(path) == 1 else completion["data"]
            _require(isinstance(outcome, dict) and type(outcome.get("attempted")) is bool,
                     f"{list(path)}: missing actual attempted status")
            observed["outcome"] = _outcome(outcome)
            observed["attempted"] = outcome["attempted"]
            observed["status"] = "attempted" if outcome["attempted"] else "not_attempted"
            if len(path) == 1:
                observed["published"] = enclosing
            else:
                _require(type(outcome.get("staged")) is bool
                         and outcome.get("publication") == "pending enclosing cell",
                         f"{list(path)}: child lost its actual staged publication")
                observed["staged"] = outcome["staged"]
                staged = [(actual.get(path[:length], {}).get("completion") or {}).get("data", {}).get("staged")
                          for length in range(2, len(path) + 1)]
                observed["published"] = (False if enclosing is False or False in staged else
                                         True if enclosing is True and all(value is True for value in staged)
                                         else None)
        elif path in skipped:
            observed.update(status="skipped", attempted=False, published=False)
            observed["eventrefs"]["scope_stop"] = skipped[path]["sequence"]
        else:
            unattempted = None
            for length in range(len(path) - 1, 0, -1):
                ancestor = actual.get(path[:length])
                completion = ancestor.get("completion") if ancestor else None
                outcome = (completion["data"].get("result") if length == 1 else completion["data"]
                           ) if completion else None
                if isinstance(outcome, dict) and outcome.get("attempted") is False:
                    unattempted = completion
                    break
            if unattempted is not None:
                observed.update(status="not_attempted", attempted=False, published=False)
                observed["eventrefs"]["enclosing_timing"] = unattempted["sequence"]
            else:
                errors.append(f"{list(path)}: source occurrence has neither native timing nor an explicit unattempted boundary")

    by_span = {(item["position"]["startByte"], item["position"]["stopByte"]): path
               for path, item in nodes.items()}
    for path in siblings[()]:
        completion = actual.get(path, {}).get("completion")
        if completion is None:
            continue
        for observation in completion["data"].get("children", []):
            if observation.get("attempted") is not True:
                continue
            position = observation.get("position", {})
            child = by_span.get((position.get("startByte"), position.get("stopByte")))
            child_row = actual.get(child)
            if (child is None or child[:1] != path or position.get("file") != file
                    or child_row is None or child_row.get("completion") is None):
                errors.append(f"{list(path)}: an attempted native child observation has no source-bound timing")
    return claimed


def reconcile(file_records: list[dict], rows: list[dict], stops: list[dict]) -> dict:
    """Build a full report from native evidence, retaining failures as failures."""
    result = {"schema": 1, "complete": True, "files": [], "errors": []}
    claimed, identities = set(), set()
    for record in file_records:
        key = (record["session"], record["file_run"])
        report = {"file": record["file"], "source_sha256": None, "session": key[0], "file_run": key[1],
                  "complete": False, "compact": None, "occurrences": [], "errors": []}
        result["files"].append(report)
        if key in identities:
            report["errors"].append("duplicate native file execution")
        identities.add(key)
        if record.get("complete") is not True:
            report["errors"].append("native file timing is incomplete")
        selected = [row for row in rows if (row.get("session"), row.get("file_run")) == key]
        try:
            claimed.update(_reconcile_file(report, record, selected, stops))
        except (KeyError, TypeError, ValueError, UnicodeError) as error:
            report["errors"].append(str(error))
        report["complete"] = not report["errors"]
    direct_starts = {(row["session"], row["start"]["sequence"]) for row in rows
                     if row.get("file_run") is None and row.get("start") is not None}
    for stop in stops:
        key = (stop.get("session"), stop.get("sequence"))
        direct = any((stop.get("session"), parent) in direct_starts for parent in stop.get("parents", []))
        if key not in claimed and not direct:
            result["errors"].append("scope stop has no reconciled native source scope")
    result["complete"] = not result["errors"] and all(file["complete"] for file in result["files"])
    return result


def _same(candidate: object, expected: object) -> bool:
    if isinstance(expected, dict):
        return (isinstance(candidate, dict) and candidate.keys() == expected.keys()
                and all(_same(candidate[key], value) for key, value in expected.items()))
    if isinstance(expected, list):
        return (isinstance(candidate, list) and len(candidate) == len(expected)
                and all(_same(left, right) for left, right in zip(candidate, expected)))
    if type(expected) in (int, float, Decimal):
        return type(candidate) in (int, float, Decimal) and candidate == expected
    return type(candidate) is type(expected) and candidate == expected


def check_report(candidate: dict, *, file_records: list[dict], rows: list[dict], stops: list[dict]) -> None:
    """Validate an actual report copy against freshly collected native evidence."""
    expected = reconcile(file_records, rows, stops)
    _require(expected["complete"], "source occurrence evidence is incomplete")
    _require(_same(candidate, expected), "source occurrence report differs from its ordered native evidence")
