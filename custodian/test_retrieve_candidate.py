import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from retrieve_candidate import retrieve
from review import review as reviewer
import verify


class CandidateRetrievalTest(unittest.TestCase):
    def test_exact_source_is_data_and_links_never_reach_the_reviewer_workspace(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root/'source'
            source.mkdir()
            def git(*args):
                return subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-C', str(source), *args],
                                      check=True, capture_output=True, text=True).stdout.strip()
            git('init', '-q', '-b', 'main')
            git('config', 'user.name', 'fixture')
            git('config', 'user.email', 'fixture@example.test')
            marker = root/'candidate-executed'
            script = source/'candidate.py'
            script.write_text('from pathlib import Path\nPath('+repr(str(marker))+').touch()\n')
            (source/'lake-manifest.json').write_text(json.dumps({'packages': []}))
            git('add', '.')
            git('commit', '-qm', 'candidate data')
            commit = git('rev-parse', 'HEAD')
            destination = root/'retrieved'
            retrieve(str(source), 'refs/heads/main', commit, destination)
            self.assertEqual((destination/'candidate.py').read_bytes(), script.read_bytes())
            self.assertEqual(subprocess.run(['git', '-C', str(destination), 'rev-parse', 'HEAD'],
                                           check=True, capture_output=True, text=True).stdout.strip(), commit)
            frozen = root/'review-snapshot'
            captured = reviewer.snapshot(verify, destination, frozen)
            self.assertEqual(captured['repository'], commit)
            self.assertEqual((frozen/'candidate.py').read_bytes(), script.read_bytes())
            self.assertFalse(marker.exists())
            (source/'linked').symlink_to(root)
            git('add', 'linked')
            git('commit', '-qm', 'hostile link')
            hostile = git('rev-parse', 'HEAD')
            with self.assertRaises(ValueError):
                retrieve(str(source), 'refs/heads/main', hostile, root/'hostile')
            self.assertFalse((root/'hostile'/'linked').exists())
            with self.assertRaises(ValueError):
                retrieve(str(source), 'refs/heads/main', commit, root/'moved-ref')
            self.assertFalse((root/'moved-ref'/'candidate.py').exists())


if __name__ == '__main__':
    unittest.main()
