"""Isolated engineering checks for existing-runtime preparation."""
import contextlib
import hashlib
import importlib.util
import io
import json
import shlex
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

SOURCE = Path(__file__).with_name('ci_kernel_candidate.py')
spec = importlib.util.spec_from_file_location('candidate', SOURCE)
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)


def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True,
                                   stderr=subprocess.DEVNULL).strip()


def commit(path):
    git(path, 'add', '.')
    git(path, 'commit', '-m', 'Fixture source')
    return git(path, 'rev-parse', 'HEAD')


def repository(path):
    path.mkdir()
    git(path, 'init', '-q')
    git(path, 'config', 'user.name', 'Preparation test')
    git(path, 'config', 'user.email', 'test@example.invalid')
    git(path, 'config', 'commit.gpgsign', 'false')
    git(path, 'config', 'core.hooksPath', str(path / 'fixture-hooks'))


def write(path, value):
    path.write_text(json.dumps(value))


def fixture(base):
    root, dependency, runtime = (base / name for name in ['kernel', 'dependency', 'runtime'])
    repository(dependency)
    (dependency / 'lakefile.lean').write_text('-- test dependency\n')
    write(dependency / 'lake-manifest.json', {})
    revision = commit(dependency)
    repository(root)
    (root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
    row = dict(name='sample', type='git', rev=revision, subDir=None,
               url='https://example.invalid/sample.git', inherited=False, scope='',
               configFile='lakefile.lean', manifestFile='lake-manifest.json')
    write(root / 'lake-manifest.json', {'packages': [row]})
    protected = root / 'tests/acceptance/original.txt'
    protected.parent.mkdir(parents=True)
    protected.write_text('original independent assertion\n')
    baseline = commit(root)
    runtime.mkdir()
    selected = {key: row[key] for key in ['name', 'inherited', 'scope', 'configFile', 'manifestFile']}
    selected.update(type='path', dir=str(dependency))
    write(runtime / 'packages.json', {'schemaVersion': '1.2.0', 'packages': [selected]})
    toolchain = runtime / 'toolchain/bin'
    toolchain.mkdir(parents=True)
    lake = toolchain / 'lake'
    lake.write_text('''#!/usr/bin/env bash
set -eu
if [[ "$1" != --packages=* ]]; then exit 9; fi
shift
if [[ "$1" != env ]]; then exit 9; fi
if [[ "$2" == lean ]]; then
  echo 'Lean (version 4.33.0, test fixture)'
elif [[ "$2" == lake ]]; then
  echo 'Lake version test (Lean version 4.33.0)'
else exit 9
fi
''')
    lake.chmod(0o755)
    (runtime / 'lake.sh').write_text('#!/usr/bin/env bash\nset -euo pipefail\n' +
        'export PATH=' + shlex.quote(str(toolchain)) + ':"$PATH"\n' +
        'cd -- ' + shlex.quote(str(root)) + '\nexec ' + shlex.quote(str(lake)) +
        ' --packages=' + shlex.quote(str(runtime / 'packages.json')) + ' "$@"\n')
    for name in ['evidence', 'cache-extraction-originals', 'engines', 'artifacts']:
        (runtime / name).mkdir()
        (runtime / name / 'preserve.txt').write_text('original ' + name)
    return root, dependency, runtime, baseline


def files(path):
    return {str(p.relative_to(path)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in path.rglob('*') if p.is_file()}


def overrides(runtime, update):
    path = runtime / 'packages.json'
    data = json.loads(path.read_text())
    update(data)
    write(path, data)


def run_case(name, mutate=None, error=None):
    with tempfile.TemporaryDirectory(prefix='candidate-reuse-') as directory:
        root, dependency, runtime, baseline = fixture(Path(directory))
        if mutate:
            mutate(root, dependency, runtime)
        before = files(runtime)
        with contextlib.redirect_stdout(io.StringIO()):
            try:
                candidate.prepare_existing(root, runtime, baseline)
            except SystemExit as failure:
                assert error and error in str(failure), (name, str(failure), error)
                assert files(runtime) == before, name + ': failed validation changed runtime/evidence'
            else:
                assert not error, name + ': invalid candidate accepted'
                evidence = runtime / 'evidence'
                after = files(runtime)
                archives = list((runtime / 'evidence-archive').iterdir())
                assert len(archives) == 1
                for preserved in ['evidence', 'cache-extraction-originals']:
                    old = archives[0] / preserved / 'preserve.txt'
                    assert hashlib.sha256(old.read_bytes()).hexdigest() == before[preserved + '/preserve.txt']
                for preserved in ['engines/preserve.txt', 'artifacts/preserve.txt', 'lake.sh', 'packages.json']:
                    assert before[preserved] == after[preserved]
                assert not (evidence / 'preserve.txt').exists()
                assert not list(evidence.glob('*-provenance.json'))
                assert not (evidence / 'candidate-summary.json').exists()
                assert candidate.snapshot(runtime) == json.loads((evidence / 'source-tuple-before.json').read_text())
                config = json.loads((evidence / 'configuration.json').read_text())
                for key in ['manifest', 'toolchain', 'overrides', 'helper', 'wrapper']:
                    assert candidate.record(config[key]['path']) == config[key]
        return name


def changed_revision(root, dependency, runtime):
    (dependency / 'lakefile.lean').write_text('-- later independent revision\n')
    commit(dependency)


def changed_protected(root, dependency, runtime):
    (root / 'tests/acceptance/original.txt').write_text('changed assertion\n')
    commit(root)


def wrong_subdirectory(root, dependency, runtime):
    sub = dependency / 'other'
    sub.mkdir()
    overrides(runtime, lambda data: data['packages'][0].update(dir=str(sub)))


cases = [
    ('valid existing runtime', None, None),
    ('duplicate package', lambda r, d, t: overrides(t, lambda x: x['packages'].append(dict(x['packages'][0]))), 'exactly once'),
    ('missing package', lambda r, d, t: overrides(t, lambda x: x['packages'].clear()), 'exactly once'),
    ('extra package', lambda r, d, t: overrides(t, lambda x: x['packages'].append({**x['packages'][0], 'name': 'extra'})), 'exactly once'),
    ('wrong wrapper checkout', lambda r, d, t: (t / 'lake.sh').write_text((t / 'lake.sh').read_text().replace('cd -- ' + str(r), 'cd -- ' + str(r.parent / 'other-kernel'))), 'different checkout'),
    ('wrong wrapper overrides', lambda r, d, t: (t / 'lake.sh').write_text((t / 'lake.sh').read_text().replace('--packages=' + str(t / 'packages.json'), '--packages=' + str(t / 'other-packages.json'))), 'different checkout'),
    ('wrong revision', changed_revision, 'committed revision'),
    ('dirty dependency', lambda r, d, t: (d / 'lakefile.lean').write_text('-- uncommitted\n'), 'committed revision'),
    ('wrong subdirectory', wrong_subdirectory, 'committed subdirectory'),
    ('wrong config field', lambda r, d, t: overrides(t, lambda x: x['packages'][0].update(configFile='other.lean')), 'committed declaration'),
    ('wrong toolchain', lambda r, d, t: (t / 'toolchain/bin/lake').write_text((t / 'toolchain/bin/lake').read_text().replace('4.33.0', '4.33.1')), 'does not match lean-toolchain'),
    ('dirty kernel', lambda r, d, t: (r / 'uncommitted.txt').write_text('uncommitted'), 'checkout is not clean'),
    ('changed protected input', changed_protected, 'Protected assertions'),
]
class ExistingRuntimePreparationTests(unittest.TestCase):
    def test_preservation_and_rejection_boundaries(self):
        for case in cases:
            with self.subTest(case=case[0]):
                run_case(*case)

    def test_source_change_during_input_reading(self):
        with tempfile.TemporaryDirectory(prefix='candidate-reuse-race-') as directory:
            root, dependency, runtime, baseline = fixture(Path(directory))
            before = files(runtime)
            original_git = candidate.git
            changed = False

            def racing_git(path, *args):
                nonlocal changed
                result = original_git(path, *args)
                if path == root and args[:2] == ('diff', '--name-status') and not changed:
                    changed = True
                    changed_protected(root, dependency, runtime)
                return result

            with mock.patch.object(candidate, 'git', side_effect=racing_git):
                with self.assertRaisesRegex(SystemExit, 'changed during reuse preparation'):
                    candidate.prepare_existing(root, runtime, baseline)
            self.assertTrue(changed)
            self.assertEqual(files(runtime), before)


if __name__ == '__main__':
    unittest.main()
