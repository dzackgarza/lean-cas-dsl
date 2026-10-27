#!/usr/bin/env python3
"""Build one published candidate at its committed dependency manifest.

This produces engineering records only. It does not update dependencies, change
protected assertions, run admission, or replace the independent acceptance gate.
Sources and build products stay separate from the uploaded provenance/logs.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shlex
import shutil
import subprocess
import time


def stamp():
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args], text=True).strip()


def record(path):
    path = Path(path)
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return {'path': str(path), 'sha256': digest.hexdigest(), 'bytes': path.stat().st_size}


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def state(path):
    return {'path': str(path), 'commit': git(path, 'rev-parse', 'HEAD'),
            'tree': git(path, 'rev-parse', 'HEAD^{tree}'),
            'workingTree': git(path, 'status', '--porcelain')}


def snapshot(runtime):
    roots = json.loads((runtime / 'evidence/source-roots.json').read_text())
    return {name: state(Path(path)) for name, path in roots.items()}


def prepare(root, runtime, baseline):
    evidence = runtime / 'evidence'
    evidence.mkdir(parents=True)
    manifest_path = root / 'lake-manifest.json'
    manifest = json.loads(manifest_path.read_text())
    changed = git(root, 'diff', '--name-status', baseline, 'HEAD', '--',
                  'tests/acceptance', 'CasAcceptance/Permanent')
    write(evidence / 'protected-inputs.json', {
        'baseline': git(root, 'rev-parse', baseline), 'changed': changed,
        'scope': ['tests/acceptance', 'CasAcceptance/Permanent'],
        'meaning': 'Preservation check against the received V1 checkpoint; no admission or migration'})
    if changed:
        raise SystemExit('Protected assertions or their independent input records changed:\n' + changed)
    if state(root)['workingTree']:
        raise SystemExit('Candidate checkout is not clean')

    def restore(row):
        name, revision = row['name'], row['rev']
        if Path(name).name != name or name in {'.', '..'} or not re.fullmatch('[0-9a-f]{40}', revision):
            raise SystemExit('Manifest must select safe package names and exact commit IDs')
        directory = runtime / 'dependencies' / name
        log = evidence / ('fetch-' + name + '.log')
        with log.open('x') as output:
            for command in [
                    ['git', 'init', str(directory)],
                    ['git', '-C', str(directory), 'remote', 'add', 'origin', row['url']],
                    ['git', '-C', str(directory), 'fetch', '--depth', '1', 'origin', revision],
                    ['git', '-C', str(directory), 'checkout', '--detach', 'FETCH_HEAD']]:
                subprocess.run(command, check=True, stdout=output, stderr=subprocess.STDOUT)
        if git(directory, 'rev-parse', 'HEAD') != revision:
            raise SystemExit('Fetched dependency differs from its committed selection')
        subdir = Path(row.get('subDir') or '.')
        if subdir.is_absolute() or '..' in subdir.parts:
            raise SystemExit('Dependency subdirectory escapes its repository')
        selected = directory / subdir
        if not (selected / row['configFile']).is_file():
            raise SystemExit('Selected dependency configuration is absent')
        return directory, {
            'name': name, 'dir': str(selected), 'type': 'path',
            **{key: row[key] for key in ['inherited', 'scope', 'configFile', 'manifestFile']}}

    with ThreadPoolExecutor(max_workers=4) as pool:
        restored = list(pool.map(restore, manifest['packages']))
    overrides = {'schemaVersion': '1.2.0', 'packages': [row for _, row in restored]}
    write(runtime / 'packages.json', overrides)
    aliases = {'lean_categories': 'mathematics', 'cas_leaf_contracts': 'contract',
               'mathlib': 'mathlib', '«nbdsl-worker»': 'notebook'}
    roots = {'kernel': str(root)}
    roots.update({aliases.get(row['name'], 'dependency:' + row['name']): str(directory)
                  for directory, row in restored})
    write(evidence / 'source-roots.json', roots)
    initial = snapshot(runtime)
    if any(item['workingTree'] for item in initial.values()):
        raise SystemExit('A selected dependency is not clean')
    write(evidence / 'source-tuple-before.json', initial)
    wrapper = runtime / 'lake.sh'
    wrapper.write_text('#!/usr/bin/env bash\nset -euo pipefail\ncd -- ' +
                       shlex.quote(str(root)) + '\nexec lake --packages=' +
                       shlex.quote(str(runtime / 'packages.json')) + ' "$@"\n')
    write(evidence / 'configuration.json', {
        'manifest': record(manifest_path), 'toolchain': record(root / 'lean-toolchain'),
        'overrides': record(runtime / 'packages.json'), 'helper': record(__file__),
        'wrapper': record(wrapper), 'githubRun': os.environ.get('GITHUB_RUN_ID'),
        'githubAttempt': os.environ.get('GITHUB_RUN_ATTEMPT')})
    shutil.copyfile(runtime / 'packages.json', evidence / 'packages.json')
    shutil.copyfile(wrapper, evidence / 'lake.sh')
    print(json.dumps({'prepared': initial, 'packages': str(runtime / 'packages.json')}), flush=True)


def run(root, runtime, name, command):
    evidence = runtime / 'evidence'
    log = evidence / (name + '.log')
    report_path = evidence / (name + '-provenance.json')
    if log.exists() or report_path.exists():
        raise SystemExit('Refuse to overwrite a candidate execution record: ' + name)
    before = snapshot(runtime)
    initial = json.loads((evidence / 'source-tuple-before.json').read_text())
    if before != initial:
        raise SystemExit('Selected source changed before ' + name)
    report = {'purpose': 'Candidate engineering verification; no acceptance authority inferred',
              'producer': before, 'publishedKernel': before['kernel']['commit'],
              'command': command, 'startedUtc': stamp(), 'status': 'running',
              'runtimeEnvironment': {key: os.environ.get(key) for key in
                  ['LEAN_NUM_THREADS', 'CAS_SAGE_PYTHON', 'CAS_GAP_PYTHON',
                   'CAS_LEAF_CONTRACT_PATH', 'PYTHONPATH', 'DOT_SAGE', 'MPLCONFIGDIR']}}
    write(report_path, report)
    start = time.monotonic()
    with log.open('x') as output:
        process = subprocess.Popen(command, cwd=root, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, bufsize=1)
        for line in process.stdout:
            output.write(line)
            output.flush()
            print(line, end='', flush=True)
        code = process.wait()
    after = snapshot(runtime)
    report.update(status='completed', exit=code, finishedUtc=stamp(),
                  seconds=round(time.monotonic() - start, 3), producerAfter=after,
                  sourceTupleChanged=before != after, log=record(log),
                  peakChildRssKiB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    write(report_path, report)
    if code or before != after:
        raise SystemExit(code or 2)


def cache(root, runtime):
    selected = {row['name']: Path(row['dir'])
                for row in json.loads((runtime / 'packages.json').read_text())['packages']}
    paths = [root, *selected.values()]
    prefixes = {'Mathlib', 'Aesop', 'Qq', 'Batteries', 'ProofWidgets',
                'LeanSearchClient', 'ImportGraph', 'Plausible'}
    pattern = re.compile(r'^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?'
                         r'([A-Za-z_][A-Za-z_0-9.]*)\s*$', re.M)
    seen, targets = set(), set()

    def visit(path):
        if path in seen:
            return
        seen.add(path)
        for module in pattern.findall(path.read_text()):
            if module.split('.')[0] in prefixes:
                targets.add(module)
                continue
            for base in paths:
                source = base / (module.replace('.', '/') + '.lean')
                if source.is_file():
                    visit(source)
                    break

    for path in root.glob('Cas*.lean'):
        visit(path)
    for directory in root.glob('Cas*'):
        if directory.is_dir():
            for path in directory.rglob('*.lean'):
                visit(path)
    write(runtime / 'evidence/cache-inputs.json', {'sourceFiles': len(seen), 'modules': sorted(targets)})
    run(root, runtime, 'mathlib-cache',
        ['bash', str(runtime / 'lake.sh'), 'exe', 'cache', 'get', *sorted(targets)])
    # The upstream cache stores auxiliary packages under .lake/packages. Bind the
    # extracted build products to the same exact path-selected dependency sources.
    relocations = []
    extracted = root / '.lake/packages'
    backup = runtime / 'cache-extraction-originals'
    backup.mkdir()
    for package in extracted.iterdir() if extracted.exists() else []:
        if package.is_symlink():
            continue
        if sorted(item.name for item in package.iterdir()) != ['.lake'] or package.name not in selected:
            raise SystemExit('Unexpected upstream cache extraction layout: ' + str(package))
        destination = selected[package.name]
        shutil.copytree(package / '.lake', destination / '.lake', dirs_exist_ok=True)
        original = backup / package.name
        package.rename(original)
        package.symlink_to(destination, target_is_directory=True)
        relocations.append({'package': package.name, 'selected': str(destination),
                            'originalArtifacts': str(original)})
    write(runtime / 'evidence/cache-artifact-locations.json', relocations)


def verify(root, runtime):
    evidence = runtime / 'evidence'
    before = json.loads((evidence / 'source-tuple-before.json').read_text())
    after = snapshot(runtime)
    configuration = json.loads((evidence / 'configuration.json').read_text())
    changes = [name for name in ['manifest', 'toolchain', 'overrides', 'helper', 'wrapper']
               if record(configuration[name]['path']) != configuration[name]]
    required = ['no-leaves-selftest', 'no-leaves', 'permanent-assertions', 'engine-install',
                'mathlib-cache', 'consumers', 'native', 'axiom-audit']
    stages = {}
    for name in required:
        path = evidence / (name + '-provenance.json')
        item = json.loads(path.read_text()) if path.exists() else {}
        stages[name] = {'completed': item.get('status') == 'completed',
                        'exit': item.get('exit'),
                        'sourceTupleChanged': item.get('sourceTupleChanged')}
    products = [root / '.lake/build/bin' / name for name in
                ['cas-registry-export', 'cas-axiom-audit', 'cas-harness', 'cas-question-export']]
    packages = json.loads((runtime / 'packages.json').read_text())['packages']
    worker = Path(next(row['dir'] for row in packages if row['name'] == '«nbdsl-worker»'))
    products += [worker / '.lake/build/bin/nbdsl_worker',
                 root / '.lake/build/lib/lean/CasDsl/Notebook.olean']
    missing = [str(path) for path in products if not path.is_file()]
    engines = evidence / 'engines.json'
    success = before == after and not changes and not missing and engines.is_file() and all(
        item == {'completed': True, 'exit': 0, 'sourceTupleChanged': False}
        for item in stages.values())
    write(evidence / 'source-tuple-after.json', after)
    write(evidence / 'candidate-summary.json', {
        'purpose': 'Candidate build and engineering gates only; not MVP or mathematical acceptance',
        'producer': before, 'finishedUtc': stamp(), 'stages': stages,
        'sourceTupleChanged': before != after, 'configurationChanges': changes,
        'engines': record(engines) if engines.is_file() else {'missing': True},
        'products': [record(path) for path in products if path.is_file()],
        'missingProducts': missing, 'completeBuildAtUnchangedSource': success})
    if not success:
        raise SystemExit('Candidate build incomplete or source/configuration changed; inspect uploaded records')


def reader_preflight(root, runtime, baseline=None):
    """Read the two unchanged RX-LIFT cases; never manufacture a prior identity.

    The computation-only empty harness must reach the previously recorded tuple
    constructor gap. This does not claim that the mathematical assertions ran.
    Historical question comparison is a separate observation when an earlier
    input is supplied. Missing historical input is reported explicitly and
    cannot be replaced by this run's output or claimed as semantic acceptance.
    """
    evidence = runtime / 'evidence'
    input_path = root / ('tests/acceptance/proposals/'
                         'independent-extension-reconstruction-20261024/'
                         'completion/rx-lift-prescribed-stages.cas')
    driver = root / 'scripts/probes/rx_lift_reader_preflight.lean'
    report = evidence / 'rx-lift-reader-preflight.json'
    summary_path = evidence / 'rx-lift-reader-preflight-summary.json'
    expected = {
        'reconstructed_extensions_20261024.complete.lift.first_factor_sample_one': 73,
        'reconstructed_extensions_20261024.complete.lift.first_factor_sample_two': 76,
    }
    if report.exists() or summary_path.exists():
        raise SystemExit('Refuse to overwrite a reader preflight')
    inputs = {'originalSource': record(input_path), 'driver': record(driver)}
    baseline_problem = None
    prior = {}
    if baseline is None:
        baseline_problem = 'Historical canonical question input is unavailable'
    else:
        baseline = Path(baseline).resolve()
        try:
            inputs['questionBaseline'] = record(baseline)
            document = json.loads(baseline.read_text())
            rows = document.get('readings') if isinstance(document, dict) else document
            if not isinstance(rows, list):
                raise ValueError('question baseline must be a reading array')
            for identity in expected:
                matches = [row for row in rows if isinstance(row, dict)
                           and row.get('id') == identity]
                if len(matches) != 1 or not isinstance(matches[0].get('question'), str) \
                        or not matches[0]['question']:
                    raise ValueError('missing or duplicate complete baseline for ' + identity)
                prior[identity] = matches[0]['question']
        except (OSError, ValueError) as error:
            baseline_problem = str(error)
    write(evidence / 'rx-lift-reader-preflight-inputs.json', inputs)
    command = ['env', 'CAS_READER_INPUT=' + str(input_path),
               'CAS_READER_REPORT=' + str(report), 'bash', str(runtime / 'lake.sh'),
               'env', 'lean', str(driver)]
    process_exit = None
    try:
        run(root, runtime, 'rx-lift-reader-preflight', command)
    except SystemExit as error:
        process_exit = error.code
    problems = []
    if process_exit is not None:
        problems.append('reader invocation failed: ' + str(process_exit))
    observations = []
    try:
        rows = json.loads(report.read_text())
        if not isinstance(rows, list):
            raise ValueError('reader report must be an array')
        if [row.get('id') for row in rows if isinstance(row, dict)] != list(expected):
            problems.append('report does not contain exactly the two original IDs in order')
        for row in rows:
            if not isinstance(row, dict):
                problems.append('reader report contains a malformed observation')
                continue
            identity = row.get('id')
            if identity not in expected:
                problems.append('unexpected reader identity: ' + str(identity))
                continue
            reasons = []
            if row.get('line') != expected[identity] or row.get('precedingBindings') != 32:
                reasons.append('original line or complete preceding binding scope changed')
            if row.get('maxHeartbeats') != 200000:
                reasons.append('ordinary heartbeat option changed')
            if row.get('phase') != 'evaluation' \
                    or not isinstance(row.get('question'), str) or not row['question'] \
                    or not isinstance(row.get('proposition'), str) or not row['proposition']:
                reasons.append('complete production interpretation was not retained')
            if row.get('kind') != 'gap' or row.get('fails') is not False \
                    or not isinstance(row.get('detail'), str) \
                    or 'mor.sets.tuple_cons' not in row['detail']:
                reasons.append('expected tuple constructor implementation gap was not reached')
            if row.get('dispatches') != []:
                reasons.append('reader preflight dispatched a backend request')
            same_question = (row.get('question') == prior[identity]
                             if baseline_problem is None else None)
            if same_question is False:
                reasons.append('canonical question differs byte-for-byte from the supplied baseline')
            problems.extend(identity + ': ' + reason for reason in reasons)
            observations.append({
                'id': identity, 'completeReadingAndExpectedGap': not reasons,
                'canonicalQuestionUnchanged': same_question,
                'interpretationHeartbeatTicks': row.get('interpretationHeartbeatTicks'),
                'totalHeartbeatTicks': row.get('totalHeartbeatTicks')})
    except (OSError, ValueError) as error:
        problems.append('reader report unavailable: ' + str(error))
    try:
        if any(record(item['path']) != item for item in inputs.values()):
            problems.append('a reader input changed during execution')
    except OSError as error:
        problems.append('a reader input became unavailable: ' + str(error))
    if baseline is not None and baseline_problem:
        problems.append('supplied question baseline is unusable: ' + baseline_problem)
    complete = not problems and len(observations) == 2
    write(summary_path, {
        'purpose': 'Original RX-LIFT reader preflight; no mathematical execution acceptance',
        'inputs': inputs, 'observations': observations, 'problems': problems,
        'historicalQuestionComparison': {
            'requested': baseline is not None,
            'available': baseline_problem is None, 'problem': baseline_problem},
        'completePreflight': complete,
        'report': record(report) if report.is_file() else {'missing': True}})
    for problem in problems:
        print(problem, flush=True)
    if baseline_problem:
        print('Canonical comparison not completed: ' + baseline_problem, flush=True)
    if not complete:
        raise SystemExit('RX-LIFT reader preflight is incomplete; inspect its separate report')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--runtime', type=Path,
                        default=Path(os.environ.get('RUNNER_TEMP', '/tmp')) / 'kernel-v1-candidate')
    commands = parser.add_subparsers(dest='phase', required=True)
    preparation = commands.add_parser('prepare')
    preparation.add_argument('--protected-base', required=True)
    commands.add_parser('cache')
    execution = commands.add_parser('run')
    execution.add_argument('--name', required=True)
    execution.add_argument('command', nargs=argparse.REMAINDER)
    commands.add_parser('verify')
    readers = commands.add_parser('reader-preflight')
    readers.add_argument('--question-baseline', type=Path,
                         default=os.environ.get('CAS_RX_LIFT_QUESTION_BASELINE'),
                         help='independently retained earlier complete reading array')
    args = parser.parse_args()
    root, runtime = args.root.resolve(), args.runtime.resolve()
    if args.phase == 'prepare':
        prepare(root, runtime, args.protected_base)
    elif args.phase == 'cache':
        cache(root, runtime)
    elif args.phase == 'run':
        command = args.command[1:] if args.command[:1] == ['--'] else args.command
        if not command:
            parser.error('run requires a command')
        run(root, runtime, args.name, command)
    elif args.phase == 'reader-preflight':
        reader_preflight(root, runtime, args.question_baseline)
    else:
        verify(root, runtime)


if __name__ == '__main__':
    main()
