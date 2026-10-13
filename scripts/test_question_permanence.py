"""Mechanical gate probes; no mathematical interpretation is admitted by these tests."""
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


class QuestionGate(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        self.script = scripts / "check_question_permanence.py"
        shutil.copyfile(Path(__file__).with_name("check_question_permanence.py"), self.script)
        self.base = self.root / "questions.json"
        permanent = self.root / "CasAcceptance" / "Permanent"
        permanent.mkdir(parents=True)
        self.record = permanent / "questions.json"
        self.report = self.root / "report.json"
        self.inventory = permanent / "admitted.json"
        self.base.write_text('{"a":"typed"}')
        self.record.write_text(self.base.read_text())
        self.inventory.write_text('{"assertions":{"a":"text","unread":"text"}}')
        self.report.write_text('[{"id":"a","question":"typed"}]')

    def run_gate(self, args=None):
        arguments = ["--base", str(self.base), str(self.report)] if args is None else args
        return subprocess.run(["python3", str(self.script), *arguments],
                              capture_output=True, text=True)

    def test_unread_is_required_even_without_interpretation(self):
        result = self.run_gate()
        self.assertEqual(result.returncode, 1)
        self.assertIn("ADMITTED ASSERTION MISSING: unread", result.stdout)

    def test_complete_comparison(self):
        self.inventory.write_text('{"assertions":{"a":"text"}}')
        self.assertEqual(self.run_gate().returncode, 0)
        self.report.write_text('[{"id":"a","question":"different"}]')
        result = self.run_gate()
        self.assertEqual(result.returncode, 1)
        self.assertIn("QUESTION CHANGED: a", result.stdout)

    def test_duplicate_does_not_overwrite(self):
        self.report.write_text('[{"id":"a","question":"bad"},{"id":"a","question":"typed"}]')
        result = self.run_gate()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("duplicate assertion in report: a", result.stderr)

    def test_record_mutation_has_no_command(self):
        before = self.record.read_bytes()
        self.assertEqual(self.run_gate(["--record", str(self.report)]).returncode, 2)
        self.assertEqual(self.record.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
