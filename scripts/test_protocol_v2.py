"""Exercise the public SDK through real framed child-process traffic."""

from __future__ import annotations

import json
import os
from pathlib import Path
import select
import subprocess
import sys
import unittest


ROOT = Path(__file__).resolve().parents[1]
CONTRACTS = ROOT.parent / "lean-cas-dsl-leaf-contracts"
type JsonValue = None | bool | int | float | str | list[JsonValue] | dict[str, JsonValue]


def scope_ref(slot: int) -> dict[str, JsonValue]:
    return {"ctor": "scopeRef", "args": [slot]}


class Peer:
    def __init__(self, test: unittest.TestCase):
        self.test = test
        environment = dict(os.environ, PYTHONPATH=str(CONTRACTS / "python"))
        self.process = subprocess.Popen(
            [sys.executable, str(ROOT / "scripts/probes/protocol_v2_peer.py")],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment, bufsize=0,
        )
        test.addCleanup(self.close)

    def close(self) -> None:
        assert self.process.stdin is not None
        self.process.stdin.close()
        try:
            self.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.process.kill()
            self.process.wait()
            self.test.fail("the SDK did not settle after EOF")
        finally:
            assert self.process.stdout is not None and self.process.stderr is not None
            self.process.stdout.close()
            self.process.stderr.close()

    def read_exact(self, length: int) -> bytes:
        assert self.process.stdout is not None
        result = bytearray()
        while len(result) < length:
            ready, _, _ = select.select([self.process.stdout], [], [], 5)
            self.test.assertTrue(ready, "the SDK did not produce a complete frame")
            chunk = self.process.stdout.read(length - len(result))
            if not chunk:
                assert self.process.stderr is not None
                self.test.fail("SDK channel closed: " + self.process.stderr.read().decode())
            result.extend(chunk)
        return bytes(result)

    def read(self) -> dict[str, JsonValue]:
        length = bytearray()
        while (char := self.read_exact(1)) != b"\n":
            length.extend(char)
        return json.loads(self.read_exact(int(length)))

    def send(self, value: dict[str, JsonValue]) -> dict[str, JsonValue]:
        assert self.process.stdin is not None
        payload = json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode()
        self.process.stdin.write(str(len(payload)).encode() + b"\n" + payload)
        return self.read()

    def negotiate(self) -> None:
        self.test.assertEqual(self.read(), {
            "op": "ready", "protocol": 2, "contract": "cas-computation/2",
            "features": ["scoped-values/2", "deferred/2", "suspend-resume/2"],
            "backend": "protocol-peer", "backend_version": "0",
        })
        self.test.assertEqual(self.send({"op": "hello", "protocol": 2,
                                        "contract": "cas-computation/2"}),
                              {"op": "hello", "status": "ok", "protocol": 2,
                               "contract": "cas-computation/2"})

    def invoke(self, request: int, operation: str, arguments: JsonValue) -> dict[str, JsonValue]:
        return self.send({"protocol": 2, "request_id": request, "op": operation,
                          "input": "traffic#input", "scope_id": "scope-" + str(request),
                          "args": arguments})


class ProtocolV2(unittest.TestCase):
    def test_negotiation_and_complete_immediate_frames(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        for request, value in enumerate([0, False, [], {}, None, "", "ℤ → ℚ"]):
            self.assertEqual(peer.invoke(request, "echo", value),
                             {"request_id": request, "status": "ok", "value": value,
                              "exports": []})
        self.assertEqual(peer.invoke(7, "absent", {}),
                         {"request_id": 7, "status": "unsupported", "op": "absent"})

    def test_original_proxy_rebinds_only_inside_its_resumed_generator(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        suspended = peer.invoke(0, "adaptive", {"value": scope_ref(9)})
        self.assertEqual(suspended["status"], "suspended")
        self.assertEqual(suspended["captures"], [scope_ref(9)])
        self.assertEqual(suspended["calls"], [
            {"op": "$cas.project", "args": {"value": scope_ref(9), "field": 0}}])
        self.assertEqual(suspended["exports"], [])
        reply = peer.send({"protocol": 2, "request_id": 1, "op": "$cas.resume",
                           "scope_id": "fresh", "continuation": suspended["continuation"],
                           "captures": [scope_ref(0)], "results": [scope_ref(1)]})
        self.assertEqual(reply, {"request_id": 1, "status": "ok", "exports": [],
                                 "value": {"original": scope_ref(0), "child": scope_ref(1)}})
        self.assertEqual(peer.invoke(2, "expired", {})["status"], "error")

    def test_actual_native_exports_and_request_local_disposal(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        first = peer.invoke(0, "stored", "first")["value"]["args"][0]
        second = peer.invoke(1, "stored", "second")["value"]["args"][0]
        self.assertNotEqual(first, second)
        fields = ["traffic.operation", ["parameter"],
                  {"ctor": "typedMap", "args": ["source", "target",
                                                  {"ctor": "opaqueData", "args": [first]}]},
                  "domain", "source", "target", "original-argument"]
        context = {"kind": "published", "operation": "traffic.operation", "input": "traffic#input",
                   "args": {"ctor": "apply", "args": fields}}
        # Return a fresh inline observation, not the callable token supplied in the context.
        # The handler retains every field; its opaque input token must be returned by reference.
        request = {"protocol": 2, "request_id": 2, "op": "$cas.invoke_export",
                   "scope_id": "call-first", "token": first, "context": context}
        reply = peer.send(request)
        self.assertEqual(reply["status"], "ok")
        self.assertEqual(reply["value"]["stored"], "first")
        self.assertEqual(reply["value"]["context"], context)
        self.assertEqual(peer.send({"protocol": 2, "request_id": 3, "op": "$cas.discard",
                                    "discard_request_id": 1}),
                         {"request_id": 3, "status": "ok", "disposed": True})
        request.update(request_id=4, token=second)
        self.assertEqual(peer.send(request)["status"], "error")
        request.update(request_id=5, token=first)
        self.assertEqual(peer.send(request)["status"], "ok")

    def test_duplicate_request_does_not_revoke_a_previous_export(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        token = peer.invoke(0, "stored", "retained")["value"]["args"][0]
        self.assertEqual(peer.invoke(0, "echo", "duplicate")["status"], "error")
        context = {"kind": "dependent", "prepared_role": "role", "parameters": [],
                   "bindings": [], "arguments": [], "argument_layouts": [], "result_layout": {}}
        reply = peer.send({"protocol": 2, "request_id": 1, "op": "$cas.invoke_export",
                           "scope_id": "invoke", "token": token, "context": context})
        self.assertEqual(reply["status"], "ok")
        self.assertEqual(reply["value"]["stored"], "retained")

    def test_reference_results_use_actual_input_positions(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        reply = peer.invoke(0, "references", {"item": {"content": "original"}})
        self.assertEqual(reply, {"request_id": 0, "status": "ok", "exports": [],
                                 "value": {"ctor": "inputRef", "args": [["item"]]}})

    def test_complete_deferred_groups_include_graph_actions(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        reply = peer.invoke(0, "deferred", scope_ref(6))
        self.assertEqual(reply["status"], "ok")
        self.assertEqual(reply["value"], {"ctor": "deferredData", "args": [[
            {"op": "$cas.project", "args": {"value": scope_ref(6), "field": 0}},
            {"op": "$cas.apply", "args": {"value": {"ctor": "resultRef", "args": [0]},
                                          "arguments": []}}],
            {"ctor": "resultRef", "args": [1]}]})

    def test_repeated_suspension_preserves_explicit_capture_order(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        first = peer.invoke(0, "repeated", [scope_ref(8), scope_ref(3)])
        self.assertEqual(first["captures"], [scope_ref(8), scope_ref(3)])
        second = peer.send({"protocol": 2, "request_id": 1, "op": "$cas.resume",
                            "scope_id": "second", "continuation": first["continuation"],
                            "captures": [scope_ref(0), scope_ref(1)], "results": [scope_ref(2)]})
        self.assertEqual(second["status"], "suspended")
        self.assertNotEqual(first["continuation"], second["continuation"])
        self.assertEqual(second["captures"], [scope_ref(1), scope_ref(2), scope_ref(0)])
        final = peer.send({"protocol": 2, "request_id": 2, "op": "$cas.resume",
                           "scope_id": "third", "continuation": second["continuation"],
                           "captures": [scope_ref(0), scope_ref(1), scope_ref(2)],
                           "results": [scope_ref(3)]})
        self.assertEqual(final, {"request_id": 2, "status": "ok", "exports": [],
                                 "value": [scope_ref(2), scope_ref(0), scope_ref(3)]})

    def test_resume_requires_exact_arrays_and_consumes_its_token(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        suspended = peer.invoke(0, "adaptive", {"value": scope_ref(4)})
        request = {"protocol": 2, "request_id": 1, "op": "$cas.resume", "scope_id": "bad",
                   "continuation": suspended["continuation"], "captures": [], "results": [scope_ref(0)]}
        self.assertEqual(peer.send(request)["status"], "error")
        request.update(request_id=2, scope_id="retry", captures=[scope_ref(0)], results=[scope_ref(1)])
        self.assertEqual(peer.send(request)["status"], "error")

    def test_undeclared_proxy_is_unavailable_after_resume(self) -> None:
        peer = Peer(self)
        peer.negotiate()
        suspended = peer.invoke(0, "hidden", scope_ref(2))
        self.assertEqual(suspended["captures"], [])
        reply = peer.send({"protocol": 2, "request_id": 1, "op": "$cas.resume",
                           "scope_id": "fresh", "continuation": suspended["continuation"],
                           "captures": [], "results": [scope_ref(0)]})
        self.assertEqual(reply["status"], "error")


if __name__ == "__main__":
    unittest.main()
