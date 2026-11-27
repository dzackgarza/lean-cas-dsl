"""Fixed packet peer for categorical source/continuation controls; no mathematics is computed."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from cas_port import input_ref, point_invocation, serve, typed_map
from cas_session import export, proxy

configuration = json.loads(sys.argv[1])
operation = configuration["operation"]
calls = 0


def point_response(arguments):
    global calls
    fields = point_invocation(arguments, operation)
    with Path(configuration["log"]).open("a", encoding="utf-8") as log:
        log.write(json.dumps({"op": operation, "args": arguments}) + "\n")
    calls += 1
    source = proxy(input_ref(["args", 3]))
    target = proxy(input_ref(["args", 5]))
    if configuration["mode"] == "inline":
        if calls == 1:
            assert isinstance(fields[6], dict) and fields[6].get("ctor") == "identity"
            point = configuration["point"]
            body = {"ctor": "finiteGraph", "args": [[point], [[point, point]]]}
            return {"ctor": "typedMap", "args": [
                source.reference(), target.reference(), body,
            ]}
        assert calls == 2
        returned = typed_map(fields[2])
        point = configuration["point"]
        assert returned[2] == {"ctor": "finiteGraph", "args": [[point], [[point, point]]]}
        return proxy(input_ref(["args", 6])).reference()

    assert calls == 1
    retained = []
    capture = configuration.get("capture")
    if capture is not None:
        retained.append(proxy(input_ref(capture)))

    def native_field(context):
        with Path(configuration["log"]).open("a", encoding="utf-8") as log:
            log.write(json.dumps(context) + "\n")
        assert context["kind"] == "dependent"
        assert context["prepared_role"].startswith("project:")
        if retained:
            assert context["prepared_role"].endswith(
                "CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.base"
            )
            return retained[0].reference()

        def native_nested(_context):
            raise NotImplementedError("this fixture exposes only its complete native field")

        return export(native_nested, [])

    body = export(native_field, retained)
    return {"ctor": "typedMap", "args": [source.reference(), target.reference(), body]}


serve("categorical-packet-peer", "0", {operation: point_response})
