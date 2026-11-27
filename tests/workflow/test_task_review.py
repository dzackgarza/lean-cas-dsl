import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]


class TaskReviewTests(unittest.TestCase):
    def run_review(self, report, expected_implementation):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            workflows = project / ".specify/workflows"
            shutil.copytree(ROOT / ".specify/workflows", workflows)
            agent = project / "claude"
            agent.write_text(
                "#!/bin/sh\n"
                'case "$*" in\n'
                '  *speckit.analyze*|*speckit-analyze*) touch analyzed; cat report ;;\n'
                '  *speckit.implement*|*speckit-implement*) touch implemented ;;\n'
                'esac\n'
            )
            agent.chmod(0o755)
            (project / "report").write_text(report)
            result = subprocess.run(
                ["specify", "workflow", "run", "speckit",
                 "-i", "spec=fixture", "-i", "integration=claude",
                 "-i", "speckit_review_spec_verdict=approve",
                 "-i", "speckit_review_plan_verdict=approve", "--json"],
                cwd=project, env={**os.environ, "PATH": directory + os.pathsep + os.environ["PATH"]},
                text=True, capture_output=True, check=False,
            )
            diagnostic = result.stdout + result.stderr
            self.assertTrue((project / "analyzed").exists(), diagnostic)
            self.assertEqual((project / "implemented").exists(), expected_implementation, diagnostic)
            self.assertEqual(result.returncode == 0, expected_implementation, diagnostic)

    def test_blocking_finding_stops_implementation(self):
        self.run_review("T127 requires unfinished pullback handling.\nTASK REVIEW: BLOCKED\n", False)

    def test_missing_verdict_stops_implementation(self):
        self.run_review("Incomplete analysis.\n", False)

    def test_conflicting_verdicts_stop_implementation(self):
        self.run_review("TASK REVIEW: BLOCKED\nTASK REVIEW: READY\n", False)

    def test_truncated_report_stops_implementation(self):
        self.run_review("TASK REVIEW: READY\n" + " " * 70000, False)

    def test_ready_review_reaches_implementation(self):
        self.run_review("No blocking findings.\nTASK REVIEW: READY\n", True)


if __name__ == "__main__":
    unittest.main()
