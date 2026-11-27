"""Protocol-v2 traffic provider for kernel session tests.

It answers integer-ring addition and multiplication and the cardinality of a
named finite set from its complete published method invocation. A numeral operand arrives
as its registered descriptor; the peer reads its integer. Multiplication by two is
answered by a deferred published addition on the caller's own ring parameter.
The explicit fixed-group-kernel mode supplies opaque native fields and an exact
input reference for admission checks; it performs no group computation.
"""

from __future__ import annotations

import json
import sys

from cas_port import deferred_call, deferred_data, input_ref, method_invocation, result_ref, serve
from cas_session import ComputationError, JsonValue, UnsupportedOperation, export, proxy


FIRST_ADD_FAILURE: str | None = None
LOG: str | None = None
REFERENCE_INPUTS = False
FIXED_ENDPOINT: int | None = None
if len(sys.argv) == 3 and sys.argv[1] == "--reference-add":
    REFERENCE_INPUTS = True
    LOG = sys.argv[2]
elif len(sys.argv) == 4 and sys.argv[1] == "--fixed-group-kernel" and \
        sys.argv[2] in ("left", "right"):
    FIXED_ENDPOINT = 0 if sys.argv[2] == "left" else 1
    LOG = sys.argv[3]
elif sys.argv[1:] not in ([], ["--corrupt-add"]):
    if len(sys.argv) != 4 or sys.argv[1] != "--fail-first-add" or \
            sys.argv[2] not in ("unsupported", "unavailable"):
        raise SystemExit("usage: kernel_session_peer.py "
                         "[--corrupt-add | --fail-first-add unsupported|unavailable LOG | "
                         "--reference-add LOG | --fixed-group-kernel left|right LOG]")
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

    return left + right + (1 if "--corrupt-add" in sys.argv[1:] else 0)


def multiply(context: JsonValue) -> JsonValue:
    if REFERENCE_INPUTS:
        assert LOG is not None
        with open(LOG, "a", encoding="utf-8") as log:
            log.write(json.dumps({"op": "op.rings.mul", "context": context}) + "\n")
    left, right = _operands(context)
    if right != 2:
        return left * right
    assert isinstance(context, dict)
    call = dict(context)
    call["parameters"] = [input_ref(["parameters", 0])]


    call["arguments"] = [[input_ref(["arguments", 0, 0]),
                          input_ref(["arguments", 0, 0])]] if REFERENCE_INPUTS else [[left, left]]
    return deferred_data(
        [deferred_call("op.rings.add", "op.rings.add#input", call)], result_ref(0)
    )


def cardinality(context: JsonValue) -> JsonValue:
    assert isinstance(context, dict)
    _, actions, receiver = method_invocation(context, "meth.cardinality", "fun.sets.cardinality")
    assert actions == [{"ctor": "fun.sets.cardinality", "args": []}], actions
    assert isinstance(receiver, dict) and receiver["ctor"] == "obj.sets.fin"
    size = receiver["args"]
    assert isinstance(size, list)
    return {"ctor": "finite", "args": [size[0]]}


def group_kernel(context: JsonValue) -> JsonValue:
    """Supply a whole native record, changing only its fixed original input reference."""
    assert FIXED_ENDPOINT is not None and LOG is not None
    _, actions, receiver = method_invocation(
        context, "meth.group_arrow_kernel", "fun.arrows_groups.kernel"
    )
    assert actions == [{"ctor": "fun.arrows_groups.kernel", "args": []}], actions
    assert isinstance(receiver, dict) and receiver["ctor"] == "arrow", receiver
    fields = receiver["args"]
    assert isinstance(fields, list) and len(fields) == 3, receiver
    assert fields[0] == fields[1], "the original distinct endpoints must have equal packets"
    address = ["receiver", "args", FIXED_ENDPOINT]
    with open(LOG, "a", encoding="utf-8") as log:
        log.write(json.dumps({"op": "meth.group_arrow_kernel", "context": context,
                              "ambient": address}) + "\n")

    def group_field(_context: JsonValue) -> JsonValue:
        raise NotImplementedError("the admission control supplies no group computation")



    ambient = proxy(input_ref(address))
    return [export(group_field, []), ambient.reference(), export(group_field, [])]


serve(
    "kernel-session-peer",
    "0",
    {"op.rings.add": add, "op.rings.mul": multiply, "meth.cardinality": cardinality}
    | ({"meth.group_arrow_kernel": group_kernel} if FIXED_ENDPOINT is not None else {}),
)
