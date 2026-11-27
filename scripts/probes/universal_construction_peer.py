"""Whole product cones and native mediator continuations for occurrence controls."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from cas_port import input_ref, serve
from cas_session import export, proxy, suspend

configuration = json.loads(sys.argv[1])
apex = {"ctor": "finiteData", "args": ["original-product", [[0, 0]]]}


def observe(operation, arguments):
    with Path(configuration["log"]).open("a", encoding="utf-8") as log:
        log.write(json.dumps({"op": operation, "args": arguments}) + "\n")


def construction(arguments):
    observe("lim.sets.product", arguments)
    assert arguments["ctor"] == "pair" and len(arguments["args"]) == 2
    endpoints = [proxy(input_ref(["args", index])) for index in range(2)]
    maps = [
        {"ctor": "typedMap", "args": [
            apex, endpoint.reference(),
            {"ctor": "finiteGraph", "args": [[[0, 0]], [[[0, 0], 0]]]},
        ]}
        for endpoint in endpoints
    ]
    return {"ctor": "cone", "args": [apex, *maps]}


def mediator(arguments):
    observe("lim.sets.product#isLimit", arguments)
    assert arguments["prepared_role"].endswith("IsLimit.lift")
    assert len(arguments["bindings"]) == 1 and arguments["bindings"][0]["slot"] == 0
    assert len(arguments["arguments"]) == 1
    target_cone = proxy(input_ref(["bindings", 0, "value"]))
    source_cone = proxy(input_ref(["arguments", 0]))
    points = yield suspend(
        [source_cone.project(0), target_cone.project(0)],
        [source_cone, target_cone],
    )
    source, target = points
    if configuration["mode"] == "wrong-target":
        target = source

    def apply_mediator(context):
        observe("mediator-application", context)
        assert len(context["arguments"]) == 1
        return input_ref(["arguments", 0])

    return {"ctor": "typedMap", "args": [
        source.reference(), target.reference(),
        export(apply_mediator, [source, target]),
    ]}


serve("universal-construction-peer", "0", {
    "lim.sets.product": construction,
    "lim.sets.product#isLimit": mediator,
})
