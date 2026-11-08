"""Protocol-only traffic through the unchanged pinned v1 SDK."""

from __future__ import annotations

import json
import os
from pathlib import Path
import sys

import cas_port

type JsonValue = None | bool | int | float | str | list[JsonValue] | dict[str, JsonValue]

record = Path(sys.argv[1])
with record.open("a") as output:
    output.write(str(os.getpid()) + "\n")
values: dict[str, JsonValue] = {}


def echo(arguments: JsonValue) -> JsonValue:
    return arguments


def state(arguments: JsonValue) -> JsonValue:
    return {"pid": os.getpid(), "cwd": os.getcwd(), "helper": cas_port.__file__,
            "contract": os.environ["CAS_LEAF_CONTRACT_PATH"],
            "probe": os.environ["CAS_BRIDGE_PROBE"], "arguments": arguments}


def retain(arguments: JsonValue) -> JsonValue:
    token = f"original-{len(values)}"
    values[token] = arguments
    return cas_port.opaque_data(token)


def invoke(arguments: JsonValue) -> JsonValue:
    fields = cas_port.point_invocation(arguments, "traffic.invoke")
    _, _, callable_data = cas_port.typed_map(fields[2])
    token = callable_data["args"][0]
    return {"retained": values[token], "context": json.dumps(fields, ensure_ascii=False)}


def fail(arguments: JsonValue) -> JsonValue:
    raise ArithmeticError("original computational failure")


cas_port.serve("original-traffic", "0", "pinned-v1", {
    "traffic.echo": echo, "traffic.state": state, "traffic.retain": retain,
    "traffic.invoke": invoke, "traffic.fail": fail,
})
