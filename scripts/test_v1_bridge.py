"""Explicit bridge preparation and unchanged v1 child traffic, without mathematics."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
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


if __name__ == "__main__":
    unittest.main()
