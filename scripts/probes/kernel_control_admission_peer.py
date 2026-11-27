"""Whole-control framing peer; it supplies no mathematical answers.

Every invocation is logged. Invalid modes place a fault after a valid first
child so a consumer must reject the complete frame before running that child.
The valid mode is used only to inspect transport admission of exact captures.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from cas_port import input_ref, read_frame, result_ref, write_frame

mode, log_name = sys.argv[1:]
log_path = Path(log_name)
write_frame({"op": "ready", "protocol": 2, "contract": "cas-computation/2",
             "features": ["scoped-values/2", "deferred/2", "suspend-resume/2",
                          "export-capture-frames/2"],
             "backend": "control-admission-peer", "backend_version": "0"})
hello = read_frame()
assert hello == {"op": "hello", "protocol": 2, "contract": "cas-computation/2"}
write_frame(dict(hello, status="ok"))
while (request := read_frame()) is not None:
    with log_path.open("a", encoding="utf-8") as output:
        output.write(json.dumps(request, ensure_ascii=False) + "\n")
    rid = request["request_id"]
    if request["op"] == "$cas.discard":
        write_frame({"request_id": rid, "status": "ok", "disposed": True})
        continue
    if request["op"] != "op.rings.mul":
        write_frame({"request_id": rid, "status": "error", "kind": "UnexpectedChild",
                     "message": "the whole control should have failed before this child"})
        continue
    assert set(request) == {"protocol", "request_id", "op", "input", "args", "scope_id"}
    context = request["args"]
    reference = input_ref(["parameters", 0])
    call = {"op": "op.rings.add", "input": "op.rings.add#input", "args": context}
    calls = [call]
    captures = [reference]
    exports = []
    template = result_ref(0)
    if mode == "duplicate_capture":
        captures.append(reference)
    elif mode == "bad_export_capture":
        exports = [{"token": "local-export", "captures": [reference, reference]}]
    elif mode == "bad_later_call":
        calls.append(dict(call, owner="provider-claimed-owner"))
    elif mode == "bad_later_graph":
        calls.append({"op": "$cas.project", "args": {"value": reference, "field": 0,
                                                       "resultType": "provider-claimed-type"}})
    elif mode == "bad_template_scope":
        template = {"ctor": "scopeRef", "args": [999999]}
    elif mode == "undeclared_opaque":
        calls.append(dict(call, args={"ctor": "opaqueData", "args": ["foreign-token"]}))
    elif mode == "valid":
        captures = [input_ref(["first"]), input_ref(["second"])]
        exports = [{"token": "local-export", "captures": captures}]
        calls = [{"op": "$cas.project", "args": {"value": captures[0], "field": 0}}]
    else:
        raise ValueError(mode)
    if mode in ("bad_later_call", "bad_template_scope", "undeclared_opaque"):
        write_frame({"request_id": rid, "status": "ok",
                     "value": {"ctor": "deferredData", "args": [calls, template]},
                     "exports": exports})
    else:
        write_frame({"request_id": rid, "status": "suspended", "continuation": "continuation-0",
                     "captures": captures, "calls": calls, "exports": exports})
