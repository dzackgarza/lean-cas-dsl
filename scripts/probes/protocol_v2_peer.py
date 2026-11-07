"""Protocol traffic peer. It supplies no mathematical computation."""

from __future__ import annotations

from collections.abc import Generator

from cas_session import JsonValue, Proxy, Suspension, export, proxy, serve, suspend


def echo(arguments: JsonValue) -> JsonValue:
    return arguments


def stored(arguments: JsonValue) -> JsonValue:
    def invoke(context: JsonValue) -> JsonValue:
        return {"stored": arguments, "context": context}

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


serve("protocol-peer", "0", {"echo": echo, "stored": stored,
                              "adaptive": adaptive, "expired": expired})
