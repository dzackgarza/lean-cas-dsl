"""Dependency preparation follows main and preserves local work."""
import json
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("ci_chain.py")


class ChainTests(unittest.TestCase):
    def test_latest_main_and_dirty_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            remote = root / "remote"
            subprocess.run(["git", "init", "-q", "-b", "main", str(remote)], check=True)
            def git(*args: str) -> str:
                return subprocess.check_output(
                    ["git", "-C", str(remote), *args], text=True).strip()
            git("config", "user.name", "Chain test")
            git("config", "user.email", "chain@example.invalid")
            git("config", "commit.gpgsign", "false")
            git("config", "core.hooksPath", str(root / "fixture-hooks"))
            (remote / "value").write_text("old\n")
            git("add", "value")
            git("commit", "-qm", "old")
            old = git("rev-parse", "HEAD")
            (remote / "value").write_text("current\n")
            git("commit", "-qam", "current")
            current = git("rev-parse", "HEAD")
            checkout = root / "consumer"
            checkout.mkdir()
            names = ("lean_categories", "cas_leaf_contracts", "cas_leaves", "nbdsl-worker")
            (checkout / "lake-manifest.json").write_text(json.dumps({"packages": [
                {"name": name, "url": str(remote), "rev": old} for name in names]}))
            command = ["python3", str(SCRIPT), str(checkout)]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            for name in names:
                package = checkout / ".lake" / "packages" / name
                actual = subprocess.check_output(
                    ["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
                self.assertEqual(actual, current, name)
            (remote / "value").write_text("new main\n")
            git("commit", "-qam", "advance main")
            advanced = git("rev-parse", "HEAD")
            subprocess.run(command, check=True, capture_output=True)
            for name in names:
                package = checkout / ".lake" / "packages" / name
                actual = subprocess.check_output(
                    ["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
                self.assertEqual(actual, advanced, name)
            dirty = checkout / ".lake/packages/lean_categories/value"
            dirty.write_text("local work\n")
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(dirty.read_text(), "local work\n")
            self.assertIn("uncommitted", result.stderr)


if __name__ == "__main__":
    unittest.main()
