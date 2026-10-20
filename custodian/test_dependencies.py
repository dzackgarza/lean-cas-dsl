import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


class DependencyInvocationTest(unittest.TestCase):
    def test_launcher_reads_advancing_main_without_changing_protected_inputs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            repo = root / 'upstream'
            repo.mkdir()
            def git(*args):
                return subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-C', str(repo), *args], check=True,
                                      capture_output=True, text=True).stdout.strip()
            git('init', '-q', '-b', 'main')
            git('config', 'user.name', 'fixture')
            git('config', 'user.email', 'fixture@example.test')
            (repo / 'specs').mkdir()
            (repo / 'specs/computational-core-plan.md').write_text('`b0-authority`')
            (repo / 'meaning').write_text('original mathematics')
            git('add', '.')
            git('commit', '-qm', 'original')
            original = git('rev-parse', 'HEAD')
            config = {'requirements': {'repository': str(repo), 'commit': original},
                      'accepted': {name: {'repository': str(repo), 'url': str(repo), 'commit': original}
                                   for name in ('mathematics', 'contract', 'acceptance')},
                      'reviewer_public_key': str(root / 'unused'), 'reviewer_fingerprint': 'unused',
                      'assignments': {'b0-authority': 'acceptance'}, 'obligation': 'b0-authority',
                      'source_repository': str(repo)}
            path = root / 'config.json'
            path.write_text(json.dumps(config))
            def read():
                request = {'id': 1, 'method': 'tools/call', 'params': {
                    'name': 'read_assigned_input', 'arguments': {'input': 'mathematics', 'path': 'meaning'}}}
                result = subprocess.run(['python3', str(Path(__file__).with_name('launcher.py')),
                                         '--configuration', str(path)], input=json.dumps(request)+'\n',
                                        check=True, capture_output=True, text=True)
                snapshot = json.loads(result.stderr)
                self.assertEqual(snapshot['requirements'], original)
                self.assertEqual(snapshot['inputs'], {'mathematics': git('rev-parse', 'main'),
                                                      'contract': git('rev-parse', 'main')})
                return json.loads(result.stdout)['result']['content'][0]['text']
            self.assertEqual(read(), 'original mathematics')
            (repo / 'meaning').write_text('current mathematical main')
            git('add', '.')
            git('commit', '-qm', 'advance main')
            self.assertEqual(read(), 'current mathematical main')
            self.assertEqual(json.loads(path.read_text()), config)

    def test_stale_artifact_blocks_leaf_dispatch_after_main_advances(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            def git(*args):
                return subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-C', str(repo), *args], check=True,
                                      capture_output=True, text=True).stdout.strip()
            git('init', '-q', '-b', 'main')
            git('config', 'user.name', 'fixture')
            git('config', 'user.email', 'fixture@example.test')
            (repo / 'meaning').write_text('first')
            git('add', '.')
            git('commit', '-qm', 'first')
            original = git('rev-parse', 'HEAD')
            artifact = repo / 'public.json'
            artifact.write_text('{"operations": []}')
            (repo / 'specs').mkdir()
            (repo / 'specs/computational-core-plan.md').write_text('`b0-authority`')
            git('add', 'specs')
            git('commit', '-qm', 'requirement')
            original = git('rev-parse', 'HEAD')
            config = {'requirements': {'repository': str(repo), 'commit': original},
                      'reviewer_public_key': str(repo / 'unused'), 'reviewer_fingerprint': 'unused',
                      'assignments': {'b0-authority': 'leaf'}, 'obligation': 'b0-authority',
                      'source_repository': str(repo), 'accepted': {
                'mathematics': {'repository': str(repo), 'url': str(repo), 'commit': original},
                'contract': {'repository': str(repo), 'url': str(repo), 'commit': original},
                'public_metadata': {'repository': str(repo), 'commit': original,
                                    'artifact_file': str(artifact),
                                    'sha256': hashlib.sha256(artifact.read_bytes()).hexdigest(),
                                    'provenance': {'mathematics': original, 'contract': original}}}}
            path = repo / 'config.json'
            path.write_text(json.dumps(config))
            command = ['python3', str(Path(__file__).with_name('launcher.py')),
                       '--configuration', str(path)]
            subprocess.run(command, input='', check=True, capture_output=True, text=True)
            (repo / 'meaning').write_text('second')
            git('add', 'meaning')
            git('commit', '-qm', 'advance')
            result = subprocess.run(command, input='', capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, '')
            self.assertEqual(config['accepted']['public_metadata']['commit'], original)
            self.assertEqual(artifact.read_text(), '{"operations": []}')


if __name__ == '__main__':
    unittest.main()
