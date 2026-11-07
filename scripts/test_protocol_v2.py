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


def scope_ref(slot: int) -> dict:
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

    def read(self) -> dict:
        length = bytearray()
        while (char := self.read_exact(1)) != b"\n":
            length.extend(char)
        return json.loads(self.read_exact(int(length)))

    def send(self, value: dict) -> dict:
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

    def invoke(self, request: int, operation: str, arguments: dict | list | str | int | bool | None) -> dict:
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


if __name__ == "__main__":
    unittest.main()
