"""Mechanical gate probes; no mathematical interpretation is admitted by these tests."""
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("gate", Path(__file__).with_name("check_question_permanence.py"))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class QuestionGate(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.base = self.root / "questions.json"
        self.record = self.root / "candidate.json"
        self.report = self.root / "report.json"
        self.inventory = self.root / "admitted.json"
        self.base.write_text('{"a":"typed"}')
        self.record.write_text(self.base.read_text())
        self.inventory.write_text('{"assertions":{"a":"text","unread":"text"}}')
        self.report.write_text('[{"id":"a","question":"typed"}]')

    def run_gate(self, args=None):
        with patch.object(gate, "RECORD", self.record), patch.object(sys, "argv", ["gate"] + (args or ["--base", str(self.base), str(self.report)])):
            return gate.main()

    def test_unread_is_required_even_without_interpretation(self):
        self.assertEqual(self.run_gate(), 1)

    def test_complete_comparison(self):
        self.inventory.write_text('{"assertions":{"a":"text"}}')
        self.assertEqual(self.run_gate(), 0)
        self.report.write_text('[{"id":"a","question":"different"}]')
        self.assertEqual(self.run_gate(), 1)

    def test_duplicate_does_not_overwrite(self):
        self.report.write_text('[{"id":"a","question":"bad"},{"id":"a","question":"typed"}]')
        self.assertEqual(self.run_gate(), 1)

    def test_record_mutation_has_no_command(self):
        before = self.record.read_bytes()
        self.assertEqual(self.run_gate(["--record", str(self.report)]), 2)
        self.assertEqual(self.record.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
