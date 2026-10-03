import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

spec = importlib.util.spec_from_file_location('controller', Path(__file__).with_name('controller.py'))
C = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = C
spec.loader.exec_module(C)

class ControllerTest(unittest.TestCase):
    def test_full_snapshot_and_independent_admission(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            repo = root / 'repo'
            repo.mkdir()
            def run(*args):
                return subprocess.run(args, check=True, capture_output=True).stdout.decode().strip()
            run('git', 'init', '-q', str(repo))
            run('git', '-C', str(repo), 'config', 'user.name', 'test')
            run('git', '-C', str(repo), 'config', 'user.email', 'test@example.test')
            for p in ('SPEC.md','INTENT.md', 'specs/architecture.md', 'specs/computational-core-plan.md', 'specs/owner/convergence-process.md', 'tests/acceptance/question.json'):
                f = repo / p
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text('`b0-authority` fixed requirement\n')
            run('git', '-C', str(repo), 'add', '.')
            run('git', '-C', str(repo), 'commit', '-qm', 'base')
            base = C.Revision(repo, run('git', '-C', str(repo), 'rev-parse', 'HEAD'))
            key = root / 'key'
            run('ssh-keygen', '-q', '-t', 'ed25519', '-N', '', '-f', str(key))
            fpr = run('ssh-keygen', '-lf', str(key) + '.pub').split()[1]
            controller = C.Controller(base, {'mathematics': base, 'contract': base, 'acceptance': base}, Path(str(key)+'.pub'), fpr, {'b0-authority': 'acceptance'})
            worker = controller.assign('b0-authority')
            self.assertFalse(hasattr(worker, 'advance'))
            self.assertFalse(hasattr(worker, 'assign'))
            (repo / 'tests/acceptance/question.json').write_text('independent proposal')
            run('git', '-C', str(repo), 'add', '.')
            run('git', '-C', str(repo), 'commit', '-qm', 'proposal')
            candidate = C.Revision(repo, run('git', '-C', str(repo), 'rev-parse', 'HEAD'))
            request = controller.propose_acceptance(worker, candidate)
            self.assertEqual(request['base']['acceptance'], base.commit)
            self.assertEqual(request['candidate']['acceptance'], candidate.commit)
            self.assertIn('INTENT.md', request['source']['acceptance'])
            self.assertIn('SPEC.md', request['requirements'])
            decision = root / 'decision.json'
            import json
            decision.write_text(json.dumps({'request_id': request['request_id'], 'outcome': 'no_blocking_finding', 'findings': []}))
            run('ssh-keygen', '-Y', 'sign', '-f', str(key), '-n', 'lean-cas-custodian', str(decision))
            self.assertEqual(controller.advance(request, decision, Path(str(decision)+'.sig')), {'mathematics':base.commit,'contract':base.commit,'acceptance': candidate.commit})
            with self.assertRaises(ValueError):controller.request('b0-authority',{'acceptance':base},{'acceptance':candidate})
            request['request_id'] = 'different snapshot'
            with self.assertRaises(ValueError):
                controller.advance(request, decision, Path(str(decision)+'.sig'))

if __name__ == '__main__':
    unittest.main()
