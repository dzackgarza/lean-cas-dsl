"""Protocol traffic peer. It supplies no mathematical computation."""

from __future__ import annotations

from collections.abc import Generator
import json
import sys

from cas_session import JsonValue, Proxy, Suspension, export, invoke_routine, proxy, suspend
from cas_port import serve


def echo(arguments: JsonValue) -> JsonValue:
    return arguments


def delegated(arguments: JsonValue) -> JsonValue:
    return invoke_routine(echo, arguments)


def stored(arguments: JsonValue) -> JsonValue:
    def invoke(context: JsonValue) -> JsonValue:
        from cas_port import input_ref

        assert isinstance(context, dict)
        result: dict[str, JsonValue] = {
            "stored": arguments, "context": json.dumps(context, ensure_ascii=False)
        }
        if context.get("kind") == "dependent":
            values = context["arguments"]
            assert isinstance(values, list)
            if values:
                result["argument"] = proxy(input_ref(["arguments", 0])).reference()
        return result

    return export(invoke, [])


def captured(arguments: JsonValue) -> JsonValue:
    from cas_port import input_ref
    from contextvars import copy_context

    first = proxy(input_ref(["first"]))
    second = proxy(input_ref(["second"]))
    unretained = proxy(input_ref(["unretained"]))
    previous = copy_context()

    def invoke(context: JsonValue) -> JsonValue:
        nonlocal previous
        for read in [lambda: previous.run(first.reference), unretained.reference]:
            try:
                read()
            except ValueError:
                pass
            else:
                raise ValueError("a prior frame or undeclared capture retained authority")
        previous = copy_context()
        assert isinstance(context, dict)
        arguments = context["arguments"]
        assert isinstance(arguments, list)
        return [second.reference(), first.reference(), proxy(arguments[0]).reference()]

    return export(invoke, [first, second])


saved: Proxy | None = None


def adaptive(arguments: JsonValue) -> Generator[Suspension, list[Proxy], JsonValue]:
    global saved
    assert isinstance(arguments, dict)
    original = proxy(arguments["value"])
    saved = original
    results = yield suspend([original.project(0)], [original])
    return {"original": original.reference(), "child": results[0].reference()}


def expired(arguments: JsonValue) -> JsonValue:
    assert saved is not None
    return saved.reference()


category_saved = None


def category_result(arguments: JsonValue):
    """Use generated family metadata with actual SDK gateway occurrences."""
    from cas_port import load_interfaces

    global category_saved
    assert isinstance(arguments, dict)
    family = load_interfaces(sys.argv[2]).category("cat.groups").family(
        "morphism", "mor.groups.trivial")
    original = family.result(proxy(arguments["value"]))
    category_saved = original
    children = yield suspend([original.project(0)], [original.value])
    return {"original": original.reference(), "child": children[0].reference()}


def category_expired(arguments: JsonValue):
    assert category_saved is not None
    return category_saved.project(0)


def references(arguments: JsonValue) -> JsonValue:
    assert isinstance(arguments, dict)
    from cas_port import input_ref

    return proxy(input_ref(["item"])).reference()


def deferred(arguments: JsonValue) -> JsonValue:
    from cas_port import deferred_data, result_ref

    value = proxy(arguments)
    return deferred_data([value.project(0), {"op": "$cas.apply", "args": {
        "value": result_ref(0), "arguments": []}}], result_ref(1))


def hidden(arguments: JsonValue) -> Generator[Suspension, list[Proxy], JsonValue]:
    value = proxy(arguments)
    yield suspend([value.project(0)], [])
    return value.reference()


def repeated(arguments: JsonValue) -> Generator[Suspension, list[Proxy], JsonValue]:
    assert isinstance(arguments, list)
    first, second = [proxy(value) for value in arguments]
    result = yield suspend([first.project(0)], [first, second])
    result = yield suspend([result[0].apply([second.reference()])], [second, result[0], first])
    return [first.reference(), second.reference(), result[0].reference()]


serve("protocol-peer", "0", {"echo": echo, "delegated": delegated, "stored": stored,
                              "captured": captured,
                              "adaptive": adaptive, "expired": expired,
                              "references": references, "deferred": deferred,
                              "hidden": hidden, "repeated": repeated,
                              **({"category_result": category_result,
                                  "category_expired": category_expired}
                                 if len(sys.argv) == 3 and sys.argv[1] == "--category-interface"
                                 else {}),
                              # An opt-in fixed packet tests property observation framing only.
                              # It never inspects a group or computes a property.
                              **({"prop.is_abelian": lambda _arguments: json.loads(sys.argv[2])}
                                 if len(sys.argv) == 3 and sys.argv[1] == "--property-observation"
                                 else {})})
