"""Protocol-v2 traffic provider for kernel session tests.

It answers integer-ring addition and multiplication and the cardinality of a
named finite set from the dependent invocation context. Multiplication by two is
answered by a deferred published addition on the caller's own ring parameter.
"""

from __future__ import annotations

from cas_port import deferred_call, deferred_data, input_ref, result_ref, serve
from cas_session import JsonValue


def _operands(context: JsonValue) -> tuple[int, int]:
    assert isinstance(context, dict)
    arguments = context["arguments"]
    assert isinstance(arguments, list)
    left, right = arguments[0]
    assert isinstance(left, int) and isinstance(right, int)
    return left, right


def add(context: JsonValue) -> JsonValue:
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
