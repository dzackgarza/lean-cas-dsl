"""Protocol-v2 provider for kernel suspension tests.

It answers integer-ring addition directly. Multiplication by two suspends: the
generator asks the kernel to resolve the published addition `a + a` on the
caller's own ring, then returns a reference to that child result on resume.
"""

from __future__ import annotations

from cas_port import deferred_call, input_ref, serve
from cas_session import JsonValue, suspend


def _integer(value: JsonValue) -> int:
    """An integer operand: a returned integer, or the ring numeral descriptor of one."""
    if isinstance(value, int):
        return value
    assert isinstance(value, dict) and value["ctor"] == "num.rings", value
    number = value["args"][-1]
    assert isinstance(number, int), value
    return number


def _operands(context: JsonValue) -> tuple[int, int]:
    assert isinstance(context, dict)
    arguments = context["arguments"]
    assert isinstance(arguments, list)
    left, right = arguments[0]
    return _integer(left), _integer(right)


def add(context: JsonValue) -> JsonValue:
    left, right = _operands(context)
    return left + right


def multiply(context: JsonValue):
    left, right = _operands(context)
    assert right == 2, context
    assert isinstance(context, dict)
    call = dict(context)
    call["parameters"] = [input_ref(["parameters", 0])]
    call["arguments"] = [[left, left]]
    results = yield suspend([deferred_call("op.rings.add", "op.rings.add#input", call)], [])
    return results[0].reference()


serve("kernel-suspension-peer", "0", {"op.rings.add": add, "op.rings.mul": multiply})
