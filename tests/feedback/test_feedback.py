"""Real public-command regressions for current source-to-result feedback.

Run from the compatible kernel checkout with
python3 -m unittest discover -s tests/feedback -v.
The probes retain their sources, reports and diagnostics under .tmp/feedback-tests.
"""
from __future__ import annotations

import json
import os
import signal
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class FeedbackTests(unittest.TestCase):
    def test_warm_consumer_executes_again(self) -> None:
        manifest = ROOT / ".tmp/kernel-session-leaves.json"
        command = ["just", "loop", "CasRuntime.SessionTests"]
        if not manifest.exists():
            subprocess.run(command, cwd=ROOT, check=True)
        previous = manifest.stat().st_mtime_ns
        result = subprocess.run(command, cwd=ROOT, check=False)
        self.assertEqual(result.returncode, 0, "the original public consumer must pass")
        self.assertGreater(
            manifest.stat().st_mtime_ns,
            previous,
            "a warm loop replayed the previous elaboration instead of executing the consumer",
        )


class SuiteTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = ROOT / ".tmp/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        self.directory = Path(tempfile.mkdtemp(dir=directory))

    def run_suite(self, selection: Path) -> tuple[int, list[dict[str, object]]]:
        report = self.directory / "report.json"
        source = self.directory / "consumer.lean"
        source.write_text(
            "import LeanCategories.Catalogue\nimport CasCatalogue.TestSuite\n\n"
            f'#cas_tests "{selection.relative_to(ROOT)}" '
            f'reporting "{report.relative_to(ROOT)}"\n'
        )
        result = subprocess.run(
            ["bash", "-c",
             'source scripts/container.sh; incontainer just probe "$1"',
             "feedback-regression", str(source.relative_to(ROOT))],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
        )
        (self.directory / "consumer.log").write_text(result.stdout)
        self.assertTrue(report.is_file(), f"the public command produced no report: {result.stdout}")
        return result.returncode, json.loads(report.read_text())

    def test_empty_selection_is_a_current_failure(self) -> None:
        selected = self.directory / "empty"
        selected.mkdir()
        status, report = self.run_suite(selected)
        self.assertNotEqual(status, 0, "an empty selected suite must not succeed")
        self.assertTrue(any(row["kind"] == "internal" and row["fails"] for row in report))

    def test_missing_input_is_infrastructure_failure(self) -> None:
        status, report = self.run_suite(self.directory / "missing.cas")
        self.assertNotEqual(status, 0)
        self.assertEqual(len(report), 1)
        self.assertEqual(report[0]["kind"], "internal")
        self.assertTrue(report[0]["fails"])

    def test_duplicate_assertions_preserve_rows_and_fail(self) -> None:
        # Duplicate an unchanged admitted assertion only in this rejected input control.
        original = (ROOT / "tests/acceptance/numbers.cas").read_text()
        assertion = next(item for item in original.split("\n\n")
                         if item.startswith("test numbers.integers.sum "))
        selected = self.directory / "duplicate.cas"
        selected.write_text(assertion + "\n\n" + assertion + "\n")
        status, report = self.run_suite(selected)
        self.assertNotEqual(status, 0, "duplicate named assertions must fail the public command")
        self.assertEqual(sum(row["id"] == "numbers.integers.sum" for row in report), 2)
        self.assertTrue(any(row["kind"] == "internal" and row["fails"] for row in report))



class AcceptanceFeedbackTests(unittest.TestCase):
    def test_interrupted_worker_cannot_reuse_previous_results(self) -> None:
        # This test runs inside the research container, alongside the actual Lean worker.
        subprocess.run(["scripts/accept_files.sh", "numbers"], cwd=ROOT, check=False)
        report = ROOT / ".tmp/accept-run.json"
        prior = [row for row in json.loads(report.read_text())
                 if Path(row["file"]).name == "numbers.cas"]
        self.assertTrue(prior, "the first real selected execution must produce results")
        directory = ROOT / ".tmp/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        log = Path(tempfile.mkdtemp(dir=directory)) / "interrupted.log"
        with log.open("w") as output:
            process = subprocess.Popen(
                ["scripts/accept_files.sh", "numbers"], cwd=ROOT,
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
            )
            try:
                deadline = time.monotonic() + 300
                interrupted = False
                while process.poll() is None and time.monotonic() < deadline:
                    pending = [process.pid]
                    while pending:
                        pid = pending.pop()
                        proc = Path(f"/proc/{pid}")
                        try:
                            pending.extend(int(child) for child in
                                           (proc / f"task/{pid}/children").read_text().split())
                            arguments = (proc / "cmdline").read_bytes().decode().split("\0")
                            workers = [arg for arg in arguments if arg.endswith("/worker0.lean")]
                            if ((proc / "comm").read_text().strip() == "lean"
                                    and (proc / "cwd").resolve() == ROOT and workers):
                                current = ROOT / Path(workers[0]).with_name("numbers.json")
                                self.assertFalse(current.exists(), "the interruption was too late")
                                os.kill(pid, signal.SIGTERM)
                                interrupted = True
                                break
                        except (FileNotFoundError, ProcessLookupError):
                            continue
                    if interrupted:
                        break
                    time.sleep(0.1)
                self.assertTrue(interrupted, f"no actual acceptance worker was reached; see {log}")
                status = process.wait(timeout=60)
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    process.wait(timeout=30)
        current = [row for row in json.loads(report.read_text())
                   if Path(row["file"]).name == "numbers.cas"
                   and not row["id"].startswith("(statement)")]
        with self.subTest("worker exit"):
            self.assertNotEqual(status, 0, f"the interrupted worker was reported successful; see {log}")
        with self.subTest("current selected result"):
            self.assertEqual(current, [], "the interrupted run inherited previous selected results")


if __name__ == "__main__":
    unittest.main()
