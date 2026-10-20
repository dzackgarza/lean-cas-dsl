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


class ScopedDependencyTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.math = self.create_repository('mathematics')
        self.contract = self.create_repository('contract')
        self.original_math = self.git(self.math, 'rev-parse', 'HEAD')
        self.original_contract = self.git(self.contract, 'rev-parse', 'HEAD')
        self.config = {
            'requirements': {'repository': str(self.math), 'commit': self.original_math},
            'accepted': {
                'mathematics': {'repository': str(self.math), 'url': str(self.math), 'commit': self.original_math},
                'contract': {'repository': str(self.contract), 'url': str(self.contract), 'commit': self.original_contract},
                'acceptance': {'repository': str(self.math), 'commit': self.original_math},
                'leaves': {'repository': str(self.root/'unavailable-leaves'), 'url': str(self.root/'unavailable-leaves'), 'commit': self.original_math},
                'notebook': {'repository': str(self.root/'unavailable-notebook'), 'url': str(self.root/'unavailable-notebook'), 'commit': self.original_math},
                'public_metadata': {
                    'repository': str(self.math), 'commit': self.original_math,
                    'path': 'public.json', 'sha256': hashlib.sha256(b'{"operation": "declared"}').hexdigest(),
                    'provenance': {'mathematics': self.original_math, 'contract': self.original_contract}}},
            'reviewer_public_key': str(self.root/'unused'), 'reviewer_fingerprint': 'unused',
            'assignments': {'b0-authority': 'formalization'}, 'obligation': 'b0-authority',
            'source_repository': str(self.math)}

    def git(self, repo, *args):
        return subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-C', str(repo), *args],
                              check=True, capture_output=True, text=True).stdout.strip()

    def create_repository(self, name):
        repo = self.root/name
        repo.mkdir()
        self.git(repo, 'init', '-q', '-b', 'main')
        self.git(repo, 'config', 'user.name', 'fixture')
        self.git(repo, 'config', 'user.email', 'fixture@example.test')
        (repo/'specs').mkdir()
        (repo/'specs/computational-core-plan.md').write_text('`b0-authority`')
        (repo/'meaning').write_text(name+' original')
        (repo/'public.json').write_text('{"operation": "declared"}')
        self.git(repo, 'add', '.')
        self.git(repo, 'commit', '-qm', 'initial main')
        return repo

    def invoke(self, role, input_name, path):
        self.config['assignments']['b0-authority'] = role
        config = self.root/'launch.json'
        config.write_text(json.dumps(self.config))
        request = {'id': 1, 'method': 'tools/call', 'params': {'name': 'read_assigned_input',
                   'arguments': {'input': input_name, 'path': path}}}
        return subprocess.run(['python3', str(Path(__file__).with_name('launcher.py')),
                               '--configuration', str(config)], input=json.dumps(request)+'\n',
                              capture_output=True, text=True)

    def test_only_actual_consumers_block_on_stale_or_unavailable_inputs(self):
        initial = self.invoke('leaf', 'public_metadata', 'public.json')
        self.assertEqual(initial.returncode, 0, initial.stderr)
        self.assertEqual(json.loads(initial.stdout)['result']['content'][0]['text'], '{"operation": "declared"}')
        (self.contract/'meaning').write_text('contract current main')
        self.git(self.contract, 'add', 'meaning')
        self.git(self.contract, 'commit', '-qm', 'advance contract main')
        for role in ('formalization', 'acceptance', 'kernel'):
            result = self.invoke(role, 'mathematics', 'meaning')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['result']['content'][0]['text'], 'mathematics original')
        stale = self.invoke('leaf', 'public_metadata', 'public.json')
        self.assertNotEqual(stale.returncode, 0)
        self.assertEqual(stale.stdout, '')
        self.config['accepted']['contract']['url'] = str(self.root/'unavailable-contract')
        (self.math/'meaning').write_text('mathematics current main')
        self.git(self.math, 'add', 'meaning')
        self.git(self.math, 'commit', '-qm', 'advance mathematical main')
        result = self.invoke('formalization', 'mathematics', 'meaning')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)['result']['content'][0]['text'], 'mathematics current main')
        self.assertEqual(json.loads(result.stderr)['inputs'], {'mathematics': self.git(self.math, 'rev-parse', 'HEAD')})
        result = self.invoke('acceptance', 'mathematics', 'meaning')
        self.assertNotEqual(result.returncode, 0)

    def test_both_artifact_representations_require_complete_exact_provenance(self):
        public = self.config['accepted']['public_metadata']
        for external in (False, True):
            if external:
                public['artifact_file'] = str(self.math/'public.json')
                del public['path']
            for provenance in (None, {'mathematics': self.original_math},
                               {'contract': self.original_contract}):
                if provenance is None:
                    public.pop('provenance', None)
                else:
                    public['provenance'] = provenance
                rejected = self.invoke('leaf', 'public_metadata', 'public_operation_metadata.json' if external else 'public.json')
                self.assertNotEqual(rejected.returncode, 0)
                self.assertEqual(rejected.stdout, '')
            public['provenance'] = {'mathematics': self.original_math, 'contract': self.original_contract}
            result = self.invoke('leaf', 'public_metadata', 'public_operation_metadata.json' if external else 'public.json')
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads(result.stdout)['result']['content'][0]['text'], '{"operation": "declared"}')


if __name__ == '__main__':
    unittest.main()
