"""Regression tests for the removed self-admission channel."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).with_name("check_acceptance_permanent.py")


class PermanenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.suite = root / "suite"
        self.suite.mkdir()
        self.lean = root / "lean"
        self.lean.mkdir()
        self.source = 'test sample "independent source": assert 1 = 1'
        (self.suite / "sample.cas").write_text(self.source + "\n")
        self.accepted = root / "accepted.json"
        self.accepted.write_text(json.dumps({"assertions": {
            "sample": hashlib.sha256(self.source.encode()).hexdigest()}, "corrections": []}))
        self.candidate = root / "candidate.json"
        self.candidate.write_bytes(self.accepted.read_bytes())
        spec = importlib.util.spec_from_file_location("permanence", SCRIPT)
        self.check = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.check)
        self.check.DIR, self.check.SUITE = self.lean, self.suite
        self.check.MANIFEST = self.candidate

    def run_check(self, *args):
        with patch("sys.argv", [str(SCRIPT), *args]), contextlib.redirect_stderr(io.StringIO()):
            return self.check.main()

    def test_unchanged_assertion_passes_without_writing(self):
        before = self.candidate.read_bytes()
        self.assertEqual(self.run_check(), 0)
        self.assertEqual(self.candidate.read_bytes(), before)

    def test_candidate_readmission_does_not_change_accepted_input(self):
        (self.suite / "sample.cas").write_text(self.source.replace("1 = 1", "1 = 2"))
        self.candidate.write_text(json.dumps({"assertions": self.check.assertions()}))
        before = self.accepted.read_bytes()
        self.assertEqual(self.run_check("--base", str(self.accepted)), 1)
        self.assertEqual(self.accepted.read_bytes(), before)

    def test_deleted_assertion_is_reported(self):
        (self.suite / "sample.cas").unlink()
        self.assertEqual(self.run_check("--base", str(self.accepted)), 1)

    def test_new_assertion_requires_independent_admission(self):
        (self.suite / "other.cas").write_text('test other "source": assert 2 = 2')
        self.assertEqual(self.run_check(), 1)

    def test_role_label_cannot_enable_any_mutation_operation(self):
        before = self.candidate.read_bytes()
        with patch.dict(os.environ, {"AGENT_ROLE": "acceptance"}):
            for args in [("--admit",), ("--correct", "reason"),
                         ("--retire", "reason", "sample=other")]:
                with self.subTest(args=args), self.assertRaises(SystemExit) as error:
                    self.run_check(*args)
                self.assertEqual(error.exception.code, 2)
        self.assertEqual(self.candidate.read_bytes(), before)

    def test_missing_accepted_input_is_not_reconstructed(self):
        self.accepted.unlink()
        with self.assertRaises(FileNotFoundError):
            self.run_check("--base", str(self.accepted))


if __name__ == "__main__":
    unittest.main()
