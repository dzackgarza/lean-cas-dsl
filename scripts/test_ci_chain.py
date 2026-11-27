"""Dependency preparation follows main and preserves local work."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("ci_chain.py")


class ChainTests(unittest.TestCase):
    def test_review_chain_preserves_manifest_snapshots(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def git(repository: Path, *arguments: str) -> str:
                return subprocess.check_output(
                    ["git", "-c", "core.hooksPath=/dev/null", "-C", str(repository),
                     *arguments], text=True).strip()

            def initialize(repository: Path) -> None:
                repository.mkdir()
                git(repository, "init", "-q", "-b", "main")
                git(repository, "config", "user.name", "Chain test")
                git(repository, "config", "user.email", "chain@example.invalid")
                git(repository, "config", "commit.gpgsign", "false")

            remote = root / "remote"
            initialize(remote)
            revisions = []
            for value in ("base dependency\n", "head dependency\n", "advanced main\n"):
                (remote / "value").write_text(value)
                git(remote, "add", "value")
                git(remote, "commit", "-qm", value.strip())
                revisions.append(git(remote, "rev-parse", "HEAD"))

            names = ("lean_categories", "cas_leaf_contracts", "cas_leaves")
            snapshot = (
                "import json, sys; from pathlib import Path; "
                "sys.path.insert(0, sys.argv[1]); "
                "import verify; from review import review; "
                "print(json.dumps(review.snapshot(verify, "
                "Path(sys.argv[2]), Path(sys.argv[3]))))"
            )
            for side, revision, value in zip(
                    ("base", "head"), revisions[:2],
                    ("base dependency\n", "head dependency\n"), strict=True):
                checkout = root / side
                initialize(checkout)
                manifest = checkout / "lake-manifest.json"
                manifest.write_text(json.dumps({"packages": [
                    {"name": name, "url": remote.as_uri(), "rev": revision}
                    for name in names]}))
                original = manifest.read_bytes()
                git(checkout, "add", "lake-manifest.json")
                git(checkout, "commit", "-qm", "locked review input")
                source_revision = git(checkout, "rev-parse", "HEAD")
                command = [sys.executable, str(SCRIPT), str(checkout), "--manifest-revisions"]
                prepared = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(prepared.returncode, 0, prepared.stderr)
                self.assertEqual(manifest.read_bytes(), original)
                captured = root / (side + "-snapshot")
                result = subprocess.run(
                    [sys.executable, "-c", snapshot,
                     str(SCRIPT.parent.parent / "custodian"), str(checkout), str(captured)],
                    capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), {
                    "repository": source_revision,
                    "packages": {name: revision for name in names}})
                self.assertEqual((captured / "lake-manifest.json").read_bytes(), original)
                for name in names:
                    package = checkout / ".lake" / "packages" / name
                    frozen = captured / ".lake" / "packages" / name
                    self.assertEqual(git(package, "rev-parse", "HEAD"), revision)
                    self.assertEqual((frozen / "value").read_text(), value)
                self.assertEqual(git(checkout, "status", "--porcelain",
                                     "--untracked-files=no"), "")
                conflicting = subprocess.run(command + ["--record-resolved"],
                                             capture_output=True, text=True)
                self.assertEqual(conflicting.returncode, 2, conflicting.stderr)
                self.assertIn("not allowed with argument", conflicting.stderr)
                self.assertEqual(manifest.read_bytes(), original)
            self.assertEqual(git(remote, "rev-parse", "HEAD"), revisions[2])

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
                {"name": "«nbdsl-worker»" if name == "nbdsl-worker" else name,
                 "url": str(remote), "rev": old} for name in names] + [
                    {"name": "third_party", "url": str(remote), "rev": old}]}))
            command = ["python3", str(SCRIPT), str(checkout)]
            result = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            for name in names:
                package = checkout / ".lake" / "packages" / name
                actual = subprocess.check_output(
                    ["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
                self.assertEqual(actual, current, name)
            subprocess.run(command + ["--record-resolved"], check=True, capture_output=True)
            recorded = json.loads((checkout / "lake-manifest.json").read_text())
            self.assertEqual([entry["rev"] for entry in recorded["packages"][:-1]],
                             [current] * len(names))
            self.assertEqual(recorded["packages"][-1],
                             {"name": "third_party", "url": str(remote), "rev": old})
            self.assertFalse((checkout / ".lake/packages/third_party").exists())
            (remote / "value").write_text("new main\n")
            git("commit", "-qam", "advance main")
            advanced = git("rev-parse", "HEAD")
            subprocess.run(command, check=True, capture_output=True)
            for name in names:
                package = checkout / ".lake" / "packages" / name
                actual = subprocess.check_output(
                    ["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
                self.assertEqual(actual, advanced, name)
            dirty = checkout / ".lake/packages/nbdsl-worker/value"
            dirty.write_text("local work\n")
            result = subprocess.run(command + ["--record-resolved"], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads((checkout / "lake-manifest.json").read_text()), recorded)
            self.assertEqual(dirty.read_text(), "local work\n")
            self.assertIn("uncommitted", result.stderr)


if __name__ == "__main__":
    unittest.main()
