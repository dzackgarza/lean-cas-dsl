"""Explicit bridge preparation and unchanged v1 child traffic, without mathematics."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import unittest

CONTRACTS = Path(sys.argv.pop(1)).resolve(strict=True)
LEGACY = Path(sys.argv.pop(1)).resolve(strict=True)
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.test_protocol_v2 import Peer, scope_ref


class V1Bridge(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="cas-v1-bridge-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.leaf = self.directory / "original"
        self.leaf.mkdir()
        self.program = self.leaf / "peer.py"
        shutil.copyfile(ROOT / "scripts/probes/protocol_v1_peer.py", self.program)
        self.started = self.directory / "starts"
        self.manifest = self.leaf / "leaves.json"
        self.source = {"backends": [{"name": "original", "command": sys.executable,
                                     "args": ["peer.py", str(self.started)]}],
                       "registrations": [{"operation": "traffic.echo", "input": "traffic#input",
                                          "backend": "original"}]}
        self.manifest.write_text(json.dumps(self.source))
        self.execution = self.directory / "execution" / "leaves.json"
        self.environment = dict(os.environ, CAS_BRIDGE_PROBE="original environment",
                                PYTHONPATH=str(CONTRACTS / "python"))

    def prepare(self, legacy: Path = LEGACY) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["uv", "run", "--frozen", "--project", str(CONTRACTS), "python",
             str(CONTRACTS / "python/cas_v1_bridge.py"), "--manifest", str(self.manifest),
             "--legacy-contract", str(legacy), "--output-manifest", str(self.execution)],
            text=True, capture_output=True, timeout=15, env=self.environment,
        )

    def peer(self) -> Peer:
        prepared = self.prepare()
        self.assertEqual(prepared.returncode, 0, prepared.stderr)
        translated = json.loads(self.execution.read_text())
        backend = translated["backends"][0]
        command = [backend["command"], *backend["args"]]
        peer = Peer(self, CONTRACTS, command)
        ready = peer.read()
        self.assertEqual(ready["protocol"], 2)
        self.assertEqual(ready["backend"], "original-traffic")
        self.assertEqual(ready["features"], ["scoped-values/2", "deferred/2", "suspend-resume/2",
                                            "export-capture-frames/2"])
        self.assertEqual(peer.send({"op": "hello", "protocol": 2, "contract": "cas-computation/2"}),
                         {"op": "hello", "protocol": 2, "contract": "cas-computation/2", "status": "ok"})
        return peer

    def test_explicit_manifest_runs_one_original_child(self) -> None:
        before = {path: hashlib.sha256(path.read_bytes()).hexdigest()
                  for path in [self.manifest, self.program]}
        peer = self.peer()
        translated = json.loads(self.execution.read_text())
        self.assertEqual(translated["registrations"], self.source["registrations"])
        for request, argument in enumerate(["ℤ → ℚ", False, 0, [], {}, None]):
            self.assertEqual(peer.invoke(request, "traffic.echo", argument),
                             {"request_id": request, "status": "ok", "value": argument, "exports": []})
        state = peer.invoke(6, "traffic.state", "exact input")["value"]
        self.assertEqual(state["cwd"], str(self.leaf))
        self.assertEqual(state["helper"], str(LEGACY / "python/cas_port.py"))
        self.assertEqual(state["contract"], str(LEGACY))
        self.assertEqual(state["probe"], "original environment")
        self.assertEqual(self.started.read_text().splitlines(), [str(state["pid"])])
        self.assertEqual(peer.invoke(7, "traffic.fail", {}), {
            "request_id": 7, "status": "error", "kind": "ArithmeticError",
            "message": "original computational failure"})
        self.assertEqual(before, {path: hashlib.sha256(path.read_bytes()).hexdigest() for path in before})

    def test_native_aliases_keep_full_context_and_request_local_leases(self) -> None:
        peer = self.peer()
        first = peer.invoke(0, "traffic.retain", "original stored value")
        self.assertEqual(first["exports"], [{"token": first["value"]["args"][0], "captures": []}])
        second = peer.invoke(1, "traffic.retain", first["value"])
        token = second["value"]["args"][0]
        self.assertEqual(second["exports"], [{"token": token,
                                             "captures": [{"ctor": "inputRef", "args": [[]]}]}])
        fields = ["traffic.invoke", ["original parameter"],
                  {"ctor": "typedMap", "args": ["actual source", "actual target", second["value"]]},
                  "generalized domain", "actual source", "actual target", scope_ref(0)]
        request = {"protocol": 2, "request_id": 2, "op": "$cas.invoke_export", "token": token,
                   "scope_id": "invocation", "captures": [scope_ref(0)],
                   "context": {"kind": "published", "operation": "traffic.invoke",
                               "input": "traffic#input", "args": {"ctor": "apply", "args": fields}}}
        reply = peer.send(request)
        self.assertEqual(reply["status"], "ok")
        native = json.loads(reply["value"]["context"])
        self.assertEqual(native, ["traffic.invoke", ["original parameter"],
                         {"ctor": "typedMap", "args": ["actual source", "actual target",
                                                        {"ctor": "opaqueData", "args": ["original-1"]}]},
                         "generalized domain", "actual source", "actual target",
                         {"ctor": "opaqueData", "args": ["original-0"]}])
        unsupported = dict(request, request_id=3, context={
            "kind": "dependent", "prepared_role": "actual-role", "parameters": [],
            "bindings": [], "arguments": [], "argument_layouts": [], "result_layout": {}})
        self.assertEqual(peer.send(unsupported),
                         {"request_id": 3, "status": "unsupported", "op": "$cas.invoke_export"})
        self.assertEqual(peer.send({"protocol": 2, "request_id": 4, "op": "$cas.discard",
                                    "discard_request_id": 0})["status"], "ok")
        self.assertEqual(peer.invoke(5, "traffic.echo", first["value"])["status"], "error")
        request["request_id"] = 6
        self.assertEqual(peer.send(request)["status"], "ok")
        self.assertEqual(peer.send({"protocol": 2, "request_id": 7, "op": "$cas.discard",
                                    "discard_request_id": 1})["status"], "ok")
        request["request_id"] = 8
        self.assertEqual(peer.send(request)["status"], "error")
        self.assertEqual(peer.invoke(9, "traffic.echo", second["value"])["status"], "error")
        self.assertEqual(peer.send({"protocol": 2, "request_id": 10, "op": "$cas.resume",
                                    "scope_id": "unissued", "continuation": "unissued",
                                    "captures": [], "results": []})["status"], "error")

    def test_foreign_scope_is_unsupported_before_child_dispatch(self) -> None:
        peer = self.peer()
        self.assertEqual(peer.invoke(0, "traffic.echo", scope_ref(7)),
                         {"request_id": 0, "status": "unsupported", "op": "traffic.echo"})
        self.assertFalse(self.started.with_suffix(".calls").exists())
        self.assertEqual(peer.invoke(1, "traffic.echo", "later actual data")["value"], "later actual data")

    def test_child_loss_closes_the_wrapper_without_a_restart(self) -> None:
        peer = self.peer()
        child = peer.invoke(0, "traffic.state", {})["value"]["pid"]
        os.kill(child, signal.SIGTERM)
        self.assertNotEqual(peer.process.wait(timeout=5), 0)
        self.assertEqual(self.started.read_text().splitlines(), [str(child)])

    def test_legacy_identity_and_changed_source_reject_before_ready(self) -> None:
        refused = self.prepare(CONTRACTS)
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn("required pinned revision", refused.stderr)
        self.assertFalse(self.execution.exists())
        prepared = self.prepare()
        self.assertEqual(prepared.returncode, 0, prepared.stderr)
        backend = json.loads(self.execution.read_text())["backends"][0]
        self.program.write_text(self.program.read_text() + "\n# changed original bytes\n")
        refused = subprocess.run([backend["command"], *backend["args"]], input=b"",
                                 capture_output=True, timeout=5)
        self.assertNotEqual(refused.returncode, 0)
        self.assertEqual(refused.stdout, b"")
        self.assertIn(b"a bridge input changed", refused.stderr)
        self.assertFalse(self.started.exists())


if __name__ == "__main__":
    unittest.main()
