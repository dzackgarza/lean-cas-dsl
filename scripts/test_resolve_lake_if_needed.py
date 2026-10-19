"""Lake resolution runs only when a fetched own-organisation head changed."""

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from resolve_lake_if_needed import OWN_REQUIRES, stale_requires


class LakeResolutionTests(unittest.TestCase):
    def test_unchanged_heads_skip_resolution_and_changed_head_is_selected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            packages = root / ".lake" / "packages"
            revisions = {}
            for name in OWN_REQUIRES:
                checkout = packages / name
                subprocess.run(["git", "init", "-q", "-b", "main", str(checkout)], check=True)
                subprocess.run(["git", "-C", str(checkout), "config", "user.name", "Lake test"], check=True)
                subprocess.run(["git", "-C", str(checkout), "config", "user.email",
                                "lake@example.invalid"], check=True)
                subprocess.run(["git", "-C", str(checkout), "config", "core.hooksPath",
                                str(root / "fixture-hooks")], check=True)
                (checkout / "source").write_text(name)
                subprocess.run(["git", "-C", str(checkout), "add", "source"], check=True)
                subprocess.run(["git", "-C", str(checkout), "-c", "commit.gpgsign=false",
                                "commit", "-qm", "initial"], check=True)
                revisions[name] = subprocess.check_output(
                    ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
            manifest = {"packages": [
                {"name": "«nbdsl-worker»" if name == "nbdsl-worker" else name,
                 "rev": revisions[name]} for name in OWN_REQUIRES]}
            (root / "lake-manifest.json").write_text(json.dumps(manifest))
            self.assertEqual(stale_requires(root), [])

            (packages / "lean_categories" / "source").write_text("new main")
            subprocess.run(["git", "-C", str(packages / "lean_categories"), "commit", "-qam",
                            "advance", "--no-gpg-sign"], check=True)
            self.assertEqual(stale_requires(root), ["lean_categories"])


if __name__ == "__main__":
    unittest.main()
