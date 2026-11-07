"""Protocol traffic peer. It supplies no mathematical computation."""

from __future__ import annotations

from collections.abc import Generator
import json

from cas_session import JsonValue, Proxy, Suspension, export, proxy, suspend
from cas_port import serve


def echo(arguments: JsonValue) -> JsonValue:
    return arguments


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


serve("protocol-peer", "0", {"echo": echo, "stored": stored,
                              "adaptive": adaptive, "expired": expired,
                              "references": references, "deferred": deferred,
                              "hidden": hidden, "repeated": repeated})
