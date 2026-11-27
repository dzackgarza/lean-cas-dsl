"""Lossless native application-log transport and exact derived JSON records."""
from __future__ import annotations

import json
from decimal import Decimal
from typing import Iterator


def _unique_object(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("a JSON object has a duplicate field")
        result[key] = value
    return result


def _invalid_constant(value: str) -> None:
    raise ValueError(f"invalid JSON numeric constant {value}")


def decode_json_graph(document: object) -> object:
    """Restore exact JSON values; earlier references retain shared Python objects."""
    if not isinstance(document, dict) or set(document) != {"root", "nodes"}:
        raise ValueError("a JSON graph must contain its root and node table")
    nodes, root = document["nodes"], document["root"]
    if not isinstance(nodes, list) or type(root) is not int or not 0 <= root < len(nodes):
        raise ValueError("a JSON graph root is outside its node table")
    values: list[object] = []

    def child(index: object) -> object:
        if type(index) is not int or not 0 <= index < len(values):
            raise ValueError("a JSON graph has a forward, cyclic or missing child reference")
        return values[index]

    for node in nodes:
        if not isinstance(node, list) or not node or not isinstance(node[0], str):
            raise ValueError("a JSON graph has an invalid constructor")
        tag = node[0]
        if tag == "null" and len(node) == 1:
            value = None
        elif tag == "bool" and len(node) == 2 and type(node[1]) is bool:
            value = node[1]
        elif (tag == "num" and len(node) == 3 and type(node[1]) is int
              and type(node[2]) is int and node[2] >= 0):
            mantissa, exponent = node[1:]
            if exponent == 0:
                value = mantissa
            else:
                # Tuple construction is exact even beyond the active Decimal precision.
                digits = tuple(int(digit) for digit in str(abs(mantissa)))
                value = Decimal((int(mantissa < 0), digits, -exponent))
        elif tag == "str" and len(node) == 2 and isinstance(node[1], str):
            value = node[1]
        elif tag == "arr" and len(node) == 2 and isinstance(node[1], list):
            value = [child(index) for index in node[1]]
        elif tag == "obj" and len(node) == 2 and isinstance(node[1], list):
            value = {}
            for entry in node[1]:
                if (not isinstance(entry, list) or len(entry) != 2
                        or not isinstance(entry[0], str)):
                    raise ValueError("a JSON graph has an invalid object field")
                key, index = entry
                if key in value:
                    raise ValueError("a JSON graph has a duplicate object field")
                value[key] = child(index)
        else:
            raise ValueError("a JSON graph has an invalid constructor")
        values.append(value)
    return values[root]


def loads_application_event(line: str | bytes) -> dict:
    """Read a native wire event; the envelope is unchanged and data is expanded."""
    event = json.loads(line, parse_float=Decimal, parse_constant=_invalid_constant,
                       object_pairs_hook=_unique_object)
    if not isinstance(event, dict) or type(event.get("schema")) is not int:
        raise ValueError("invalid application log schema")
    if event["schema"] not in (1, 2):
        raise ValueError(f"unsupported application log schema {event['schema']}")
    data = event["data"]
    if event["schema"] == 2:
        event["data"] = decode_json_graph(data)
    return event


def _exact_json_parts(value: object) -> Iterator[str]:
    # An explicit stack also handles deep decoded DAGs without a recursive expansion
    # in memory. Repeated children are written at each original JSON field.
    pending = [(0, value)]
    active: set[int] = set()
    while pending:
        operation, current = pending.pop()
        if operation == 1:
            yield current
        elif operation == 2:
            active.remove(current)
        elif isinstance(current, (dict, list, tuple)):
            identity = id(current)
            if identity in active:
                raise ValueError("a derived JSON record contains a cycle")
            active.add(identity)
            pending.append((2, identity))
            if isinstance(current, dict):
                yield "{"
                pending.append((1, "}"))
                entries = list(current.items())
                for index in range(len(entries) - 1, -1, -1):
                    key, child = entries[index]
                    if not isinstance(key, str):
                        raise TypeError("a derived JSON object key is not a string")
                    pending.append((0, child))
                    pending.append((1, ": "))
                    pending.append((1, json.dumps(key, ensure_ascii=False)))
                    if index:
                        pending.append((1, ", "))
            else:
                yield "["
                pending.append((1, "]"))
                for index in range(len(current) - 1, -1, -1):
                    pending.append((0, current[index]))
                    if index:
                        pending.append((1, ", "))
        elif isinstance(current, Decimal):
            if not current.is_finite():
                raise ValueError("a derived JSON number is not finite")
            yield str(current)
        else:
            yield json.dumps(current, ensure_ascii=False, allow_nan=False)


def dumps_exact_json(value: object) -> str:
    """Write ordinary JSON, preserving decoded decimals as exact numeric literals."""
    return "".join(_exact_json_parts(value))
