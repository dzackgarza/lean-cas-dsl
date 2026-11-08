"""Original workflow source and explicit execution-manifest wiring controls."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

CONTRACTS = Path(sys.argv.pop(1)).resolve(strict=True)
LEGACY = Path(sys.argv.pop(1)).resolve(strict=True)
WORKFLOW_RUNTIME = Path(sys.argv.pop(1)).resolve(strict=True)
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import ci_kernel_candidate as candidate
import ci_kernel_workflows as workflows


class ExecutionManifests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="cas-execution-manifests-")
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.originals = [
            WORKFLOW_RUNTIME / "workflow-sources/workflowLeaves/diagnostics/v1/leaves.json",
            WORKFLOW_RUNTIME / "workflow-sources/existingLeaves/leaves.json",
        ]
        self.executions = [self.directory / name / "leaves.json" for name in ["diagnostic", "sets"]]
        for original, execution in zip(self.originals, self.executions, strict=True):
            result = self.bridge("--manifest", str(original), "--legacy-contract", str(LEGACY),
                                 "--output-manifest", str(execution))
            self.assertEqual(result.returncode, 0, result.stderr)

    def bridge(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["uv", "run", "--frozen", "--project", str(CONTRACTS), "python",
             str(CONTRACTS / "python/cas_v1_bridge.py"), *arguments],
            capture_output=True, text=True, timeout=15,
        )

    def test_contract_verifies_the_complete_original_mapping(self) -> None:
        for original, execution in zip(self.originals, self.executions, strict=True):
            result = self.bridge("--manifest", str(original), "--execution-manifest", str(execution))
            self.assertEqual(result.returncode, 0, result.stderr)
            document = json.loads(result.stdout)
            self.assertEqual(document["format"], "cas-v1-execution/1")
            paths = {item["path"] for item in document["guards"]}
            self.assertIn(str(original.resolve()), paths)
            self.assertIn(str(execution.resolve()), paths)
            for backend in json.loads(execution.read_text())["backends"]:
                self.assertIn(backend["args"][2], paths)

    def test_added_registration_is_rejected(self) -> None:
        source = json.loads(self.executions[0].read_text())
        source["registrations"].append(dict(source["registrations"][0]))
        self.executions[0].write_text(json.dumps(source))
        result = self.bridge("--manifest", str(self.originals[0]),
                             "--execution-manifest", str(self.executions[0]))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("registration", result.stderr)

    def test_descriptor_changes_invalidate_the_recorded_runner_guards(self) -> None:
        selected = candidate.execution_manifest_inputs(self.originals[0], self.executions[0], CONTRACTS)
        self.assertEqual(candidate.changed_records(selected["guards"]), [])
        backend = json.loads(self.executions[0].read_text())["backends"][0]
        descriptor = Path(backend["args"][2])
        source = json.loads(descriptor.read_text())
        source["environment"]["CAS_EXECUTION_GUARD_PROBE"] = "changed after validation"
        descriptor.write_text(json.dumps(source))
        self.assertIn(str(descriptor), candidate.changed_records(selected["guards"]))

    def test_prefetched_original_sources_are_reused_without_mutation(self) -> None:
        before = {name: candidate.state(WORKFLOW_RUNTIME / "workflow-sources" / name)
                  for name in workflows.LEAVES}
        metadata = {name: (Path(source["path"]) / ".git").read_bytes()
                    for name, source in before.items()}
        self.assertEqual(workflows.verify_workflow_sources(WORKFLOW_RUNTIME), before)
        self.assertEqual(workflows.verify_workflow_sources(WORKFLOW_RUNTIME), before)
        self.assertEqual(metadata, {name: (Path(source["path"]) / ".git").read_bytes()
                                    for name, source in before.items()})

    def test_another_prefetched_revision_is_rejected(self) -> None:
        runtime = self.directory / "wrong-runtime"
        sources = runtime / "workflow-sources"
        sources.mkdir(parents=True)
        (sources / "workflowLeaves").symlink_to(LEGACY, target_is_directory=True)
        (sources / "existingLeaves").symlink_to(self.originals[1].parent, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "exact clean revision"):
            workflows.verify_workflow_sources(runtime)

    def test_demo_preparation_uses_the_explicit_wrapper_commands(self) -> None:
        output = self.directory / "demo"
        result = subprocess.run([
            sys.executable, str(ROOT / "scripts/run_kernel_v1_demo.py"),
            "--contract", str(CONTRACTS), "--sage-python", "/sage/.venv/bin/python",
            "--diagnostic-manifest", str(self.originals[0]), "--leaves-manifest", str(self.originals[1]),
            "--diagnostic-execution-manifest", str(self.executions[0]),
            "--sets-execution-manifest", str(self.executions[1]),
            "--output", str(output), "--prepare-only",
        ], capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stderr)
        manifest = json.loads((output / "leaves.json").read_text())
        originals = [json.loads(path.read_text()) for path in self.originals]
        expected = originals[0]["registrations"] + [row for row in originals[1]["registrations"]
            if (row["operation"], row["input"], row["backend"]) in (
                ("lim.sets.pullback", "cat.sets", "sage-set-limits"),
                ("meth.cardinality", "cat.sets", "sage-set-limits"))]
        self.assertEqual(manifest["registrations"], expected)
        for backend in manifest["backends"]:
            self.assertEqual(backend["args"][0], str(CONTRACTS / "python/cas_v1_bridge.py"))
            self.assertEqual(backend["args"][1], "--legacy-command-json")
            self.assertTrue(Path(backend["args"][2]).is_absolute())
        inputs = json.loads((output / "inputs.json").read_text())
        for original in self.originals:
            self.assertIn(str(original), inputs["sources"])
        self.assertIn("executionManifests", inputs)
        self.assertFalse((output / "report.json").exists())


if __name__ == "__main__":
    unittest.main()
