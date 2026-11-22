"""Exercise acceptance comparisons through their existing command-line boundary."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("check_acceptance_regression.py")


class AcceptanceRegressionTests(unittest.TestCase):
    def test_new_holding_assertion_has_no_previous_outcome(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base, head = (Path(directory) / name for name in ("base.json", "head.json"))
            base.write_text("[]")
            head.write_text(json.dumps([
                {"file": "selected.cas", "id": "new", "kind": "holds"}
            ]))
            result = subprocess.run(
                [sys.executable, str(SCRIPT), str(base), str(head)],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("now holds", result.stdout)


if __name__ == "__main__":
    unittest.main()
