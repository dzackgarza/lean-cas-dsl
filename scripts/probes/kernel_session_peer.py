"""Protocol-v2 traffic provider for kernel session tests.

It answers integer-ring addition and multiplication and the cardinality of a
named finite set from the dependent invocation context. A numeral operand arrives
as its registered descriptor; the peer reads its integer. Multiplication by two is
answered by a deferred published addition on the caller's own ring parameter.
"""

from __future__ import annotations

import json
import sys

from cas_port import deferred_call, deferred_data, input_ref, result_ref, serve
from cas_session import ComputationError, JsonValue, UnsupportedOperation


FIRST_ADD_FAILURE: str | None = None
LOG: str | None = None
if len(sys.argv) != 1:
    if len(sys.argv) != 4 or sys.argv[1] != "--fail-first-add" or \
            sys.argv[2] not in ("unsupported", "unavailable"):
        raise SystemExit("usage: kernel_session_peer.py "
                         "[--fail-first-add unsupported|unavailable LOG]")
    FIRST_ADD_FAILURE, LOG = sys.argv[2:]


def _integer(value: JsonValue) -> int:
    """An integer operand: a returned integer, or the ring numeral descriptor of one."""
    if isinstance(value, int):
        return value
    assert isinstance(value, dict) and value["ctor"] == "num.rings", value
    arguments = value["args"]
    assert isinstance(arguments, list), value
    number = arguments[-1]
    assert isinstance(number, int), value
    return number


def _operands(context: JsonValue) -> tuple[int, int]:
    assert isinstance(context, dict)
    arguments = context["arguments"]
    assert isinstance(arguments, list)
    left, right = arguments[0]
    return _integer(left), _integer(right)


def add(context: JsonValue) -> JsonValue:
    global FIRST_ADD_FAILURE
    if LOG is not None:
        with open(LOG, "a", encoding="utf-8") as log:
            log.write(json.dumps({"op": "op.rings.add", "context": context}) + "\n")
    failure, FIRST_ADD_FAILURE = FIRST_ADD_FAILURE, None
    if failure == "unsupported":
        raise UnsupportedOperation("op.rings.add")
    if failure == "unavailable":
        raise ComputationError("session-failure-control", "first addition unavailable")
    left, right = _operands(context)
    return left + right


def multiply(context: JsonValue) -> JsonValue:
    left, right = _operands(context)
    if right != 2:
        return left * right
    assert isinstance(context, dict)
    call = dict(context)
    call["parameters"] = [input_ref(["parameters", 0])]
    call["arguments"] = [[left, left]]
    return deferred_data(
        [deferred_call("op.rings.add", "op.rings.add#input", call)], result_ref(0)
    )


def cardinality(context: JsonValue) -> JsonValue:
    assert isinstance(context, dict)
    arguments = context["arguments"]
    assert isinstance(arguments, list)
    receiver = arguments[0]
    assert isinstance(receiver, dict) and receiver["ctor"] == "obj.sets.fin"
    size = receiver["args"]
    assert isinstance(size, list)
    return {"ctor": "finite", "args": [size[0]]}


serve(
    "kernel-session-peer",
    "0",
    {"op.rings.add": add, "op.rings.mul": multiply, "meth.cardinality": cardinality},
)
