"""Real public-command regressions for current source-to-result feedback.

Run from the compatible kernel checkout with just test-feedback.
An optional unittest selector runs only the requested regression.
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
    def test_missing_consumer_invalidates_previous_report(self) -> None:
        module = "CasCatalogue.FeedbackMissingConsumer"
        source = module.replace(".", "/") + ".lean"
        self.assertFalse((ROOT / source).exists(), "the missing-source control must be absent")
        subprocess.run(
            ["just", "loop", "+CasCatalogue.TestSuite:leanArts", "ellipses"],
            cwd=ROOT, check=True,
        )
        report = ROOT / ".tmp/accept-run.json"
        previous = report.read_bytes()
        self.assertIn("ellipses.naturals", {row["id"] for row in json.loads(previous)})
        result = subprocess.run(["just", "loop", module, "ellipses"], cwd=ROOT, check=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(report.exists(), "the missing consumer left an earlier report as current")
        record = json.loads((ROOT / "timing/runs.jsonl").read_text().splitlines()[-1])
        self.assertEqual(record["targets"], [module])
        self.assertEqual(record["status"], 2)
        self.assertFalse(record["attempted"])
        self.assertTrue(all(phase["status"] is None for phase in record["phases"].values()))
        self.assertIsNone(record["inputs"][source])
        self.assertEqual(Path(ROOT / record["log"]).with_name("prior-accept-run.json").read_bytes(),
                         previous)

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
                 if Path(row["file"]).name == "numbers.cas"
                 and not row["id"].startswith("(statement)")]
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

    def test_partial_report_cannot_reuse_complete_results(self) -> None:
        # Hold only the owning shell after real workers start. Their computation continues,
        # but aggregation cannot race the mutation of this invocation's generated report.
        directory = ROOT / ".tmp/feedback-tests"
        directory.mkdir(parents=True, exist_ok=True)
        log = Path(tempfile.mkdtemp(dir=directory)) / "partial.log"
        run: Path | None = None
        stopped = False
        removed_id = ""
        with log.open("w") as output:
            process = subprocess.Popen(
                ["scripts/accept_files.sh", "ellipses", "numbers"], cwd=ROOT,
                stdout=output, stderr=subprocess.STDOUT, start_new_session=True,
            )
            try:
                # This deadline bounds test cleanup, not the product's feedback budget.
                deadline = time.monotonic() + 900
                while process.poll() is None and time.monotonic() < deadline:
                    if run is None:
                        for line in log.read_text().splitlines():
                            if line.startswith("Acceptance run: "):
                                run = (ROOT / line.removeprefix("Acceptance run: ")).resolve()
                                self.assertEqual(run.parent, ROOT / ".tmp/logs")
                                break
                    if run is not None:
                        selected_workers = {
                            str(run.relative_to(ROOT) / f"worker{worker}.lean")
                            for worker in range(2)
                        }
                        pending = [process.pid]
                        while pending:
                            pid = pending.pop()
                            proc = Path(f"/proc/{pid}")
                            try:
                                pending.extend(int(child) for child in
                                               (proc / f"task/{pid}/children").read_text().split())
                                arguments = (proc / "cmdline").read_bytes().decode().split("\0")
                                if ((proc / "comm").read_text().strip() == "lean"
                                        and (proc / "cwd").resolve() == ROOT
                                        and os.getpgid(pid) == process.pid
                                        and selected_workers.intersection(arguments)):
                                    self.assertFalse(
                                        (run / "ellipses.json").exists(),
                                        f"the report appeared before the aggregation barrier; see {log}",
                                    )
                                    os.kill(process.pid, signal.SIGSTOP)
                                    stopped = True
                                    break
                            except (FileNotFoundError, ProcessLookupError):
                                continue
                    if stopped:
                        break
                    time.sleep(0.1)
                self.assertTrue(stopped, f"no actual acceptance worker was reached; see {log}")
                self.assertIsNotNone(run)
                assert run is not None
                while time.monotonic() < deadline:
                    state = next(
                        line.split()[1] for line in
                        Path(f"/proc/{process.pid}/status").read_text().splitlines()
                        if line.startswith("State:")
                    )
                    if state == "T":
                        break
                    time.sleep(0.01)
                else:
                    self.fail(f"the owning acceptance shell did not stop; see {log}")

                selected_report = run / "ellipses.json"
                while time.monotonic() < deadline:
                    try:
                        workers = [
                            json.loads((run / f"worker{worker}.status.json").read_text())
                            for worker in range(2)
                        ]
                        original = selected_report.read_bytes()
                        rows = json.loads(original)
                        break
                    except (FileNotFoundError, json.JSONDecodeError):
                        time.sleep(0.1)
                else:
                    self.fail(f"the actual workers did not finish before cleanup; see {log}")
                self.assertTrue(
                    all(worker["status"] == 0 for worker in workers),
                    f"the unmodified real consumers must finish before report corruption: {workers}",
                )
                expected = set(json.loads(
                    (run / "ellipses.inventory.json").read_text())["assertions"])
                named = [row for row in rows if not row["id"].startswith("(statement)")]
                self.assertEqual({row["id"] for row in named}, expected)
                self.assertEqual(len(named), len(expected), "the original report must be complete")
                self.assertTrue(named, "the real selected report must contain named assertions")
                (run / "ellipses.complete.json").write_bytes(original)
                removed_id = named[0]["id"]
                partial = [row for row in rows if row["id"] != removed_id]
                selected_report.write_text(json.dumps(partial, ensure_ascii=False, indent=1) + "\n")

                os.kill(process.pid, signal.SIGCONT)
                stopped = False
                status = process.wait(timeout=max(1, deadline - time.monotonic()))
            finally:
                if stopped:
                    try:
                        os.kill(process.pid, signal.SIGCONT)
                    except ProcessLookupError:
                        pass
                if process.poll() is None:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=30)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait(timeout=30)

        current = json.loads((ROOT / ".tmp/accept-run.json").read_text())
        latest = json.loads((ROOT / "timing/acceptance.jsonl").read_text().splitlines()[-1])
        self.assertEqual(latest["run"], str(run.relative_to(ROOT)))
        self.assertNotEqual(status, 0, f"the partial selected report was accepted; see {log}")
        self.assertNotEqual(latest["status"], 0)
        self.assertFalse(latest["complete"], "a missing selected assertion is incomplete")
        errors = [row for row in current
                  if row["file"] == "tests/acceptance/ellipses.cas"
                  and row["kind"] == "internal" and row["fails"]]
        self.assertTrue(
            any(removed_id in row["detail"] and "incomplete" in row["detail"] for row in errors),
            f"the current failure must identify the omitted assertion {removed_id}: {errors}",
        )
        self.assertNotIn(removed_id, {row["id"] for row in current},
                         "an earlier complete result supplied the missing current assertion")
        self.assertLessEqual(
            {row["file"] for row in current},
            {"tests/acceptance/ellipses.cas", "tests/acceptance/numbers.cas"},
            "the selected report merged historical results from unselected inputs",
        )


if __name__ == "__main__":
    unittest.main()
