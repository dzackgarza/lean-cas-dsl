import json
import os
import shlex
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path

from retrieve_candidate import retrieve
from review import review as reviewer
import verify


class CandidateRetrievalTest(unittest.TestCase):
    def test_exact_source_can_be_retrieved_from_a_shallow_checkout(self):
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
            (source/'data.txt').write_text('original\n')
            git('add', 'data.txt')
            git('commit', '-qm', 'original data')
            earlier = git('rev-parse', 'HEAD')
            (source/'data.txt').write_text('selected complete data\n')
            git('commit', '-qam', 'selected data')
            selected = git('rev-parse', 'HEAD')
            shallow = root/'shallow'
            subprocess.run(['git', 'clone', '--quiet', '--depth', '1', source.as_uri(), str(shallow)],
                           check=True, capture_output=True)
            actual = subprocess.run(['git', '-C', str(shallow), 'rev-parse', '--is-shallow-repository'],
                                    check=True, capture_output=True, text=True).stdout.strip()
            self.assertEqual(actual, 'true')
            destination = root/'retrieved'
            retrieve(str(shallow), 'HEAD', selected, destination)
            self.assertEqual((destination/'data.txt').read_bytes(), (source/'data.txt').read_bytes())
            self.assertEqual(subprocess.run(['git', '-C', str(destination), 'rev-parse', 'HEAD'],
                                           check=True, capture_output=True, text=True).stdout.strip(), selected)
            with self.assertRaises(ValueError):
                retrieve(str(shallow), 'HEAD', earlier, root/'moved-ref')
            self.assertFalse((root/'moved-ref'/'data.txt').exists())

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
            attributes = source/'.gitattributes'
            attributes.write_text('*.py filter=reviewfixture text eol=crlf\n')
            git('add', '.gitattributes')
            git('commit', '-qm', 'candidate names an ambient filter')
            dependency_commit = git('rev-parse', 'HEAD')
            (source/'lake-manifest.json').write_text(json.dumps({'packages': [{'name': 'mathlib', 'rev': dependency_commit}]}))
            git('add', 'lake-manifest.json')
            git('commit', '-qm', 'include exact dependency snapshot')
            filtered_commit = git('rev-parse', 'HEAD')
            filtered = root/'filtered-retrieved'
            retrieve(str(source), 'refs/heads/main', filtered_commit, filtered)
            (filtered/'.lake/packages').mkdir(parents=True)
            retrieve(str(source), dependency_commit, dependency_commit, filtered/'.lake/packages/mathlib')
            filter_marker = root/'ambient-filter-executed'
            global_config = root/'global.gitconfig'
            filter_command = 'touch '+shlex.quote(str(filter_marker))+'; cat'
            for direction in ('smudge', 'clean'):
                subprocess.run(['git', 'config', '--file', str(global_config),
                                'filter.reviewfixture.'+direction, filter_command], check=True)
            environment = dict(os.environ, GIT_CONFIG_GLOBAL=str(global_config), GIT_CONFIG_NOSYSTEM='1',
                               PYTHONPATH=str(Path(__file__).resolve().parent))
            script_text = 'from pathlib import Path; import verify; from review import review; review.snapshot(verify, Path('+repr(str(filtered))+'), Path('+repr(str(root/'filtered-snapshot'))+'))'
            subprocess.run([sys.executable, '-c', script_text], env=environment,
                           check=True, capture_output=True, text=True)
            self.assertFalse(filter_marker.exists())
            self.assertEqual((root/'filtered-snapshot'/'candidate.py').read_bytes(), script.read_bytes())
            self.assertEqual((root/'filtered-snapshot'/'.lake/packages/mathlib/candidate.py').read_bytes(), script.read_bytes())
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
