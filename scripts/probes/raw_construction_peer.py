"""Fixed complete-cone packets for the original native constructor controls."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from cas_port import input_ref, serve
from cas_session import export, proxy


configuration = json.loads(sys.argv[1])
operation = "lim.sets.product"
apex = {"ctor": "finiteData", "args": ["original-product", [[0, 0]]]}


def construction(arguments):
    assert arguments["ctor"] == "pair"
    assert len(arguments["args"]) == 2
    with Path(configuration["log"]).open("a", encoding="utf-8") as log:
        log.write(json.dumps({"op": operation, "args": arguments}) + "\n")
    endpoints = [proxy(input_ref(["args", index])) for index in range(2)]

    def native_map(_context):
        raise NotImplementedError("this fixture returns the complete native map only")

    if configuration["mode"] == "opaque":
        return export(native_map, endpoints)
    maps = []
    for index in range(2):
        target = endpoints[1 - index] if configuration["mode"] == "swapped" else endpoints[index]
        if configuration["mode"] in {"owned", "wrapped-owned"}:
            body = export(native_map, [target])
        else:
            body = {"ctor": "finiteGraph", "args": [[[0, 0]], [[[0, 0], 0]]]}
        maps.append(body if configuration["mode"] == "bare" else
                    {"ctor": "typedMap", "args": [apex, target.reference(), body]})
    fields = [apex, *maps]
    if configuration["mode"] == "missing":
        fields.pop()
    result = {"ctor": "cone", "args": fields}
    if configuration["mode"].startswith("wrapped"):
        result = {"ctor": "valueData", "args": [{"ctor": "valueData", "args": [result]}]}
    return result


serve("raw-construction-peer", "0", {operation: construction})
