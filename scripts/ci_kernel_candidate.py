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
import sys
import time


FIXED_IMPORTS = (
    'LeanCategories.Catalogue.Semantics.Foundation.FiniteOrders',
    'LeanCategories.Catalogue.Semantics.Foundation.TwoSubsets',
    'LeanCategories.Catalogue.Semantics.Foundation.IntegerSquareBounds',
    'LeanCategories.Catalogue.Semantics.Algebra.CyclicQuotients',
    'LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions',
    'LeanCategories.Catalogue.Semantics.Independent.InterfaceCompletionTests',
)

PRODUCTION_MODULES = (
    'CasCatalogue.ConstrainedPoint', 'CasCatalogue.Language',
    'CasCatalogue.Realize.RuntimeSupport', 'CasCatalogue.Realize',
)


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


def production_artifacts(root):
    """Observe named outputs without substituting a cache hit for Lake validation."""
    result = {}
    for module in PRODUCTION_MODULES:
        relative = Path(module.replace('.', '/'))
        outputs = {}
        for directory in ['lib/lean', 'ir']:
            parent = root / '.lake/build' / directory / relative.parent
            for path in sorted(parent.glob(relative.name + '.*')):
                if not path.is_file():
                    continue
                info = path.stat()
                item = {'bytes': info.st_size, 'mtimeNs': info.st_mtime_ns}
                if path.suffix == '.trace':
                    item['sha256'] = record(path)['sha256']
                outputs[str(path.relative_to(root))] = item
        prefix = '.lake/build/lib/lean/' + relative.as_posix()
        result[module] = {
            'oleanAndTracePresent': all(prefix + suffix in outputs for suffix in ['.olean', '.trace']),
            'outputs': outputs}
    return result


def write_lake_wrapper(root, runtime):
    """Provide the selected Lake command for both direct and bash callers."""
    wrapper = runtime / 'lake.sh'
    wrapper.write_text('#!/usr/bin/env bash\nset -euo pipefail\ncd -- ' +
                       shlex.quote(str(root)) + '\nexec lake --packages=' +
                       shlex.quote(str(runtime / 'packages.json')) + ' "$@"\n')
    wrapper.chmod(0o755)
    return wrapper


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
    wrapper = write_lake_wrapper(root, runtime)
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
                   'CAS_LEAF_CONTRACT_PATH', 'PYTHONPATH', 'DOT_SAGE', 'MPLCONFIGDIR',
                   'MATHLIB_CACHE_DIR']}}
    if name == 'production':
        hit = os.environ.get('CAS_PRODUCTION_CACHE_HIT')
        report['productionCache'] = {
            'requestedKey': os.environ.get('CAS_PRODUCTION_CACHE_PRIMARY_KEY') or None,
            'restoredKey': os.environ.get('CAS_PRODUCTION_CACHE_MATCHED_KEY') or None,
            'exactKeyHit': hit == 'true' if hit is not None else None,
            'artifactsBefore': production_artifacts(root),
            'scope': 'Cache restoration and named-target reuse are separate observations; '
                     'dependency rebuilds remain in the build log.'}
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
    if name == 'production':
        cached = report['productionCache']
        artifacts = production_artifacts(root)
        cached['artifactsAfter'] = artifacts
        cached['targetsWithUnchangedArtifacts'] = [
            module for module in PRODUCTION_MODULES
            if code == 0 and before == after and artifacts[module]['oleanAndTracePresent']
            and cached['artifactsBefore'][module] == artifacts[module]]
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
    required = ['no-leaves-selftest', 'no-leaves', 'permanent-assertions', 'mathlib-cache',
                'production', 'engine-install', 'consumers', 'native', 'axiom-audit']
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
    # Keep the successful build receipt immutable when the final source check
    # runs after exports. Export provenance refers to this original receipt.
    summary = evidence / 'candidate-summary.json'
    if summary.exists():
        summary = evidence / 'candidate-final-summary.json'
    write(summary, {
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


def changed_records(records):
    changed = []
    for item in records:
        try:
            if record(item['path']) != item:
                changed.append(item['path'])
        except OSError:
            changed.append(item['path'])
    return changed


def export_gate(root, runtime, published):
    """Authenticate the already built combination; never build during export."""
    evidence = runtime / 'evidence'
    sources = snapshot(runtime)
    if not re.fullmatch('[0-9a-f]{40}', published) or sources['kernel']['commit'] != published:
        raise SystemExit('Export requires the complete explicit published kernel SHA at HEAD')
    if os.environ.get('GITHUB_SHA', published) != published:
        raise SystemExit('Published kernel SHA differs from the Actions checkout')
    if any(item['workingTree'] for item in sources.values()):
        raise SystemExit('Export sources must be clean')
    if any(evidence.resolve().is_relative_to(Path(item['path']).resolve())
           for item in sources.values()):
        raise SystemExit('Export output must be outside every selected source checkout')
    build_path = evidence / 'candidate-summary.json'
    build = json.loads(build_path.read_text())
    reader_path = evidence / 'rx-lift-reader-preflight-summary.json'
    reader = json.loads(reader_path.read_text())
    reader_run_path = evidence / 'rx-lift-reader-preflight-provenance.json'
    reader_run = json.loads(reader_run_path.read_text())
    if build.get('completeBuildAtUnchangedSource') is not True or build.get('producer') != sources:
        raise SystemExit('Export requires the successful coherent build at this exact source tuple')
    if reader.get('completePreflight') is not True or reader_run.get('status') != 'completed' \
            or reader_run.get('exit') != 0 or reader_run.get('sourceTupleChanged') is not False \
            or reader_run.get('producer') != sources or reader_run.get('producerAfter') != sources:
        raise SystemExit('Export requires the two original reader cases on this built combination')
    configuration = json.loads((evidence / 'configuration.json').read_text())
    guards = [configuration[name] for name in ['manifest', 'toolchain', 'overrides', 'helper', 'wrapper']]
    guards += [*build['products'], reader['report'], *reader['inputs'].values(),
               record(build_path), record(reader_path), record(reader_run_path)]
    modules = {}
    for name in ['CasCatalogue.Admission', 'CasCatalogue.Realize', 'CasTools.QuestionExport',
                 'CasContract.Port', 'LeanCategories.Catalogue', *FIXED_IMPORTS]:
        owner = ('mathematics' if name.startswith('LeanCategories.') else
                 'contract' if name.startswith('CasContract.') else 'kernel')
        path = Path(sources[owner]['path']) / '.lake/build/lib/lean' / (name.replace('.', '/') + '.olean')
        if not path.is_file():
            raise SystemExit('Missing already-built export import: ' + name)
        modules[name] = record(path.resolve())
        guards.append(modules[name])
        guards += [record(Path(str(path) + suffix).resolve()) for suffix in ['.private', '.server']
                   if Path(str(path) + suffix).is_file()]
    changes = changed_records(guards)
    if changes:
        raise SystemExit('Built/export inputs changed: ' + ', '.join(changes))
    return {'publishedKernel': published, 'publishedKernelTree': sources['kernel']['tree'],
            'producer': sources, 'verifiedBuild': record(build_path),
            'readerPreflight': record(reader_path), 'readerRun': record(reader_run_path),
            'moduleArtifacts': modules, 'guardedInputs': guards,
            'githubRun': os.environ.get('GITHUB_RUN_ID'),
            'githubAttempt': os.environ.get('GITHUB_RUN_ATTEMPT')}


def export_attempt(root, runtime, name, command):
    try:
        run(root, runtime, name, command)
        return 0
    except SystemExit as error:
        return error.code


def api_export(root, runtime, published):
    gate = export_gate(root, runtime, published)
    directory = runtime / 'evidence/public-api'
    directory.mkdir()  # A new export must never replace a prior snapshot.
    contract = Path(gate['producer']['contract']['path'])
    mathematics = Path(gate['producer']['mathematics']['path'])
    exporter = contract / 'tools/export_api.py'
    target = directory / 'declared-ports.json'
    inputs = [record(exporter), record(contract / 'tools/export_declared_ports.lean'),
              record(contract / 'tools/export_admission_addresses.lean'),
              record(contract / 'api/declared-ports.json')]
    command = [sys.executable, str(exporter), str(root), '--mathematics', str(mathematics),
               '--packages', str(runtime / 'packages.json'), '--output', str(target)]
    for module in FIXED_IMPORTS:
        command.extend(['--import', module])
    write(directory / 'inputs.json', {**gate, 'exporterInputs': inputs,
                                    'additionalImports': list(FIXED_IMPORTS), 'command': command})
    code = export_attempt(root, runtime, 'public-api-export', command)
    problems = [] if code == 0 else ['API exporter failed: ' + str(code)]
    provenance = None
    try:
        document = json.loads(target.read_text())
        provenance = document['provenance']
        for key, expected in {
                'kernelRevision': published,
                'mathematicsRevision': gate['producer']['mathematics']['commit'],
                'protocolRevision': gate['producer']['contract']['commit'],
                'exporterSha256': inputs[1]['sha256'],
                'addressExporterSha256': inputs[2]['sha256'],
                'admissionSourceSha256': record(root / 'CasCatalogue/Admission.lean')['sha256'],
                'additionalImports': list(FIXED_IMPORTS)}.items():
            if provenance.get(key) != expected:
                problems.append('API provenance differs at ' + key)
        for key in ['operations', 'inputForms']:
            if not isinstance(document.get(key), list) or not document[key]:
                problems.append('API has no complete ' + key + ' inventory')
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        problems.append('API output unavailable or malformed: ' + str(error))
    changes = changed_records([*gate['guardedInputs'], *inputs])
    if changes:
        problems.append('export inputs or built artifacts changed: ' + ', '.join(changes))
    write(directory / 'summary.json', {
        'purpose': 'Fresh public API documentation; no publication, admission or semantic acceptance',
        **gate, 'exporterInputs': inputs, 'exportExit': code, 'provenance': provenance,
        'output': record(target) if target.is_file() else {'missing': True},
        'problems': problems, 'completeExport': not problems})
    if problems:
        raise SystemExit('\n'.join(problems))


def question_sources(paths):
    """Record original ID/line locations without interpreting or changing syntax."""
    result = {}
    for path in sorted(paths):
        for line, source in enumerate(path.read_text().splitlines(), 1):
            match = re.match(r'^test\s+(\S+)\s+"', source)
            if match:
                identity = match[1]
                if identity in result:
                    raise SystemExit('Duplicate fixed source ID: ' + identity)
                result[identity] = {'file': str(path), 'sourceLine': line}
    return result


def check_question_export(readings, failures, expected, imports, gate, control=False):
    """Engineering completeness only; full typed terms remain separate review inputs."""
    problems, rows, document = [], [], {}
    try:
        rows = json.loads(readings.read_text())
        document = json.loads(failures.read_text())
        if not isinstance(rows, list) or not isinstance(document, dict):
            raise ValueError('expected reading array and structured failure document')
        if [row.get('id') for row in rows if isinstance(row, dict)] != list(expected):
            problems.append('missing, duplicate, reordered or unexpected fixed question IDs')
        unread = []
        for row in rows:
            if not isinstance(row, dict) or row.get('id') not in expected:
                raise ValueError('malformed or unexpected reading record')
            identity = row['id']
            if any(row.get(key) != value for key, value in expected[identity].items()):
                problems.append('original source location differs: ' + identity)
            if not isinstance(row.get('question'), str) or not isinstance(row.get('proposition'), str):
                raise ValueError('missing full typed question or proposition field: ' + identity)
            if not row['question'].strip() or not row['proposition'].strip():
                unread.append(identity)
        diagnostics = document.get('failures')
        if not isinstance(diagnostics, list):
            raise ValueError('missing structured failures array')
        for failure in diagnostics:
            if not isinstance(failure, dict) or any(
                    not isinstance(failure.get(key), str) or not failure[key]
                    for key in ['file', 'id', 'stage', 'kind', 'detail']):
                raise ValueError('malformed stage-specific failure')
        if document.get('requiredCount') != len(expected) \
                or document.get('readableCount') != len(expected) - len(unread) \
                or document.get('unreadableIds') != sorted(unread):
            problems.append('failure document does not account for the complete fixed inventory')
        provenance = document.get('provenance', {})
        selected_imports = ['Init', 'Init', 'CasTools.QuestionExport', 'CasTools.QuestionExport']
        selected_imports += [module for module in imports for _ in range(2)]
        if provenance.get('imports') != selected_imports or not provenance.get('leanVersion'):
            problems.append('production import scope or Lean provenance changed')
        module_files = provenance.get('moduleFiles', [])
        observed = ['CasCatalogue.Realize', 'LeanCategories.Catalogue', 'CasContract.Port',
                    *selected_imports]
        if [item.get('module') for item in module_files] != observed:
            problems.append('loaded module provenance is incomplete')
        for item in module_files:
            if item['module'] in gate['moduleArtifacts']:
                artifact = gate['moduleArtifacts'][item['module']]
                if Path(item['olean']).resolve() != Path(artifact['path']).resolve():
                    problems.append('loaded artifact differs from built tuple: ' + item['module'])
        if control:
            # Preserve the independently identified ambiguous binding and each
            # resulting failure. Do not invent successful readings for its scope.
            if not any(f.get('id') == 'K' and f.get('sourceLine') == 14
                       and f.get('source') == 'let K := projection.ker()'
                       and f['stage'] == 'binding' and f['kind'] == 'ambiguous'
                       and all(name in f['detail'] for name in ['meth.group_arrow_kernel', 'meth.arrow_ker'])
                       for f in diagnostics):
                problems.append('original RX08 binding ambiguity is absent')
            if any(f['kind'] != 'ambiguous' for f in diagnostics):
                problems.append('original RX08 has a failure other than its preserved ambiguity')
            if any(not any(f['id'] == identity and f['stage'] == 'interpretation'
                           and f['kind'] == 'ambiguous' for f in diagnostics)
                   for identity in unread):
                problems.append('original RX08 has an unread question without its ambiguity diagnostic')
        elif unread or diagnostics:
            problems.append('some fixed questions or their original binding contexts were not fully read')
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        problems.append('question export unavailable or malformed: ' + str(error))
    if not isinstance(rows, list):
        rows = []
    if not isinstance(document, dict):
        document = {}
    return {'requiredCount': len(expected), 'readingRecordCount': len(rows),
            'reportedReadableCount': document.get('readableCount'),
            'problems': problems, 'completeExport': not problems,
            'readings': record(readings) if readings.is_file() else {'missing': True},
            'failures': record(failures) if failures.is_file() else {'missing': True}}


def questions_export(root, runtime, published):
    gate = export_gate(root, runtime, published)
    directory = runtime / 'evidence/pure-questions'
    directory.mkdir()
    fixture_path = root / 'scripts/probes/fixed_question_export_inputs.json'
    fixture = json.loads(fixture_path.read_text())
    inputs = [record(fixture_path)]
    permanent = []
    selected = directory / 'positive-clarified'
    selected.mkdir()
    for item in fixture['permanentSources']:
        source = root / item['source']
        receipt = record(source)
        if receipt['sha256'] != item['sha256']:
            raise SystemExit('Fixed permanent source differs from the archived input: ' + str(source))
        inputs.append(receipt)
        permanent.append(source)
    if sorted(permanent) != sorted((root / 'tests/acceptance').glob('*.cas')):
        raise SystemExit('Permanent source file selection differs from the archived scope')
    original = None
    for item in fixture['extensionSources']:
        source = root / item['source']
        receipt = record(source)
        if receipt['sha256'] != item['sha256']:
            raise SystemExit('Fixed proposal differs from the archived input: ' + str(source))
        destination = selected / item['selectedName']
        shutil.copyfile(source, destination)
        inputs += [receipt, record(destination)]
        if 'originalSource' in item:
            original = root / item['originalSource']
            for path, digest in [(original, item['originalSha256']),
                                 (root / item['assessment'], item['assessmentSha256'])]:
                receipt = record(path)
                if receipt['sha256'] != digest:
                    raise SystemExit('Original RX08 or its independent clarification changed: ' + str(path))
                inputs.append(receipt)
    if original is None or len(fixture['extensionSources']) != 14:
        raise SystemExit('Missing complete archived source selection and original RX08 control')
    permanent_inventory = root / 'CasAcceptance/Permanent/admitted.json'
    inputs.append(record(permanent_inventory))
    permanent_ids = json.loads(permanent_inventory.read_text())['assertions']
    fixed_inventory = directory / 'fixed-inventory.json'
    write(fixed_inventory, {'assertions': fixture['assertions']})
    original_inventory = directory / 'rx08-original-inventory.json'
    original_ids = question_sources([original])
    write(original_inventory, {'assertions': {identity: fixture['assertions'][identity]
                                            for identity in original_ids}})
    inputs += [record(fixed_inventory), record(original_inventory)]
    selections = [
        ('permanent', root / 'tests/acceptance', permanent_inventory,
         question_sources(permanent), permanent_ids, 153, (), False),
        ('fixed-positive', selected, fixed_inventory, question_sources(list(selected.glob('*.cas'))),
         fixture['assertions'], 134, FIXED_IMPORTS, False),
        ('rx08-original-control', original, original_inventory, original_ids,
         original_ids, 7, FIXED_IMPORTS, True)]
    for name, _, _, expected, inventory, count, _, _ in selections:
        if len(expected) != count or len(inventory) != count or set(expected) != set(inventory):
            raise SystemExit('Fixed source IDs do not match the retained inventory: ' + name)
    write(directory / 'inputs.json', {**gate, 'sourceInputs': inputs,
                                    'scope': {row[0]: row[3] for row in selections}})
    summaries = {}
    for name, suite, inventory, expected, _, _, imports, control in selections:
        readings, failures = directory / (name + '.json'), directory / (name + '-failures.json')
        template = root / 'scripts/probes' / ('fixed_question_export.lean.in' if imports
                                             else 'permanent_question_export.lean.in')
        text = template.read_text()
        for key, path in [('suite', suite), ('inventory', inventory),
                          ('readings', readings), ('failures', failures)]:
            text = text.replace('"@' + key + '@"', json.dumps(str(path)))
        driver = directory / (name + '.lean')
        driver.write_text(text)
        inputs += [record(template), record(driver)]
        code = export_attempt(root, runtime, 'questions-' + name,
                              ['bash', str(runtime / 'lake.sh'), 'env', 'lean', str(driver)])
        summary = check_question_export(readings, failures, expected, imports, gate, control)
        if code != (1 if control else 0):
            summary['problems'].append('unexpected production exporter exit: ' + str(code))
        summary.update(exportExit=code, driver=record(driver), template=record(template),
                       completeExport=not summary['problems'])
        summaries[name] = summary
    changes = changed_records([*gate['guardedInputs'], *inputs])
    complete = not changes and all(item['completeExport'] for item in summaries.values())
    write(directory / 'summary.json', {
        'purpose': 'Complete pure reading exports for independent comparison; no meaning or migration verdict',
        **gate, 'sourceInputs': inputs, 'exports': summaries, 'changedInputs': changes,
        'completeExports': complete, 'independentMeaningAssessment': 'required separately'})
    if not complete:
        raise SystemExit('Pure question export incomplete; inspect full readings and separate failures')


def check_fixed_execution(document, expected):
    """A successful process or a nonfailing gap is not a completed fixed computation."""
    if not isinstance(document, list):
        return ['fixed execution did not produce a result array']
    problems = []
    if [row.get('id') for row in document if isinstance(row, dict)] != list(expected):
        problems.append('missing, duplicate, reordered or unexpected fixed assertion IDs')
    for row in document:
        if not isinstance(row, dict) or row.get('id') not in expected:
            problems.append('malformed or unexpected fixed execution result')
            continue
        identity = row['id']
        if row.get('file') != expected[identity]['file']:
            problems.append('fixed execution source differs: ' + identity)
        if row.get('kind') != 'holds' or row.get('fails') is not False:
            problems.append(identity + ': ' + str(row.get('kind')) + ': ' + str(row.get('detail', '')))
        if any(not isinstance(row.get(key), str) or not row[key].strip()
               for key in ['question', 'proposition']):
            problems.append('fixed execution omitted its complete reading: ' + identity)
        if not isinstance(row.get('dispatches'), list):
            problems.append('fixed execution omitted dispatch records: ' + identity)
    return problems


def check_fixed_controls(name, document):
    """Check the existing controls' complete results in addition to their exit code."""
    if name == 'rx10':
        if not isinstance(document, dict) or not isinstance(document.get('observations'), list):
            return ['RX10 did not produce its six-condition report']
        rows = document['observations']
        conditions = ['holds', 'gap', 'unavailable', 'malformed', 'wrong', 'internal']
        if any(not isinstance(row, dict) for row in rows) \
                or [row.get('condition') for row in rows] != conditions:
            return ['RX10 omitted, duplicated or reordered a fixed execution condition']
        problems = []
        for row in rows:
            condition = row['condition']
            if row.get('kind') != condition or row.get('expectedKind') != condition:
                problems.append('RX10 ' + condition + ' observed ' + str(row.get('kind')))
            if row.get('sameIndependentTypedQuestion') is not True:
                problems.append('RX10 lost independent question agreement: ' + condition)
            if any(not isinstance(row.get(key), str) or not row[key].strip()
                   for key in ['id', 'question', 'proposition']):
                problems.append('RX10 omitted its original complete question: ' + condition)
            if any(row.get(key) != rows[0].get(key)
                   for key in ['id', 'source', 'sourceLine', 'question', 'proposition']):
                problems.append('RX10 changed its original question: ' + condition)
            if condition in {'holds', 'wrong'} and row.get('callableReused') is not True:
                problems.append('RX10 did not consume its returned callable: ' + condition)
            if condition == 'holds' and (not isinstance(row.get('sessionControls'), dict)
                                        or row['sessionControls'].get('kind') != 'holds'):
                problems.append('RX10 did not complete the original session controls')
        return problems
    if not isinstance(document, list) or len(document) != 1 \
            or not isinstance(document[0], dict) or document[0].get('control') != name.upper():
        return [name.upper() + ' did not produce its selected complete control report']
    row = document[0]
    if name == 'rx05':
        environments = row.get('environments', [])
        if not isinstance(environments, list) or any(not isinstance(item, dict) for item in environments) \
                or [item.get('environment') for item in environments] != [
                    'present', 'present-reversed', 'absent', 'absent-reversed']:
            return ['RX05 did not retain all four declaration environments']
        checks = row.get('crossEnvironmentChecks', {})
        required = ['presentResolutionMetadataEqual', 'presentCompleteTypedRequestsEquivalent',
                    'absentCompleteCandidatesEquivalentAsMultisets',
                    'registryApplicableInventoriesEquivalentAsMultisets']
        if not isinstance(checks, dict) or any(checks.get(key) is not True for key in required):
            return ['RX05 did not complete its original full typed comparisons']
        for index, environment in enumerate(environments):
            if not isinstance(environment.get('selectedInventory'), dict) \
                    or not isinstance(environment.get('typedReceiver'), dict):
                return ['RX05 omitted the selected inventory or complete receiver']
            if index < 2:
                if environment.get('resolutionKind') != 'resolved' \
                        or not isinstance(environment.get('typedRequest'), dict):
                    return ['RX05 omitted a complete selected comparison request']
            elif environment.get('resolutionKind') != 'ambiguous' \
                    or environment.get('completeRegistryInventoryRetained') is not True \
                    or not isinstance(environment.get('candidates'), list) \
                    or not environment['candidates'] \
                    or not isinstance(environment.get('registryApplicableCandidates'), list) \
                    or not environment['registryApplicableCandidates']:
                return ['RX05 omitted its complete actual ambiguity inventory']
        return []
    if name == 'rx09':
        if row.get('kind') != 'invalid' or row.get('stage') != 'admission' \
                or row.get('prerequisites') != 4 or row.get('dispatches') != [] \
                or not isinstance(row.get('actualAttempt'), dict) \
                or not isinstance(row.get('independentObligation'), dict):
            return ['RX09 did not retain its exact typed negative admission observation']
        return []
    raise ValueError('Unknown fixed control: ' + name)


def fixed_execution(root, runtime, published, manifest, leaf_commit, controls=False):
    """Run existing fixed inputs unchanged; this does not admit or rewrite an assertion."""
    gate = export_gate(root, runtime, published)
    manifest = manifest.resolve()
    leaf_root = Path(git(manifest.parent, 'rev-parse', '--show-toplevel')).resolve()
    leaf = state(leaf_root)
    if not re.fullmatch('[0-9a-f]{40}', leaf_commit) or leaf['commit'] != leaf_commit \
            or leaf['workingTree'] or not manifest.is_relative_to(leaf_root):
        raise SystemExit('Fixed execution requires the exact clean frozen leaf checkout')
    name = 'fixed-controls' if controls else 'fixed-execution'
    directory = runtime / 'evidence' / name
    directory.mkdir()
    guards = [*gate['guardedInputs'], record(__file__), record(manifest)]
    invocations = []
    if controls:
        for control, module in [('rx10', 'FixedQuestionExecutionControls'),
                                ('rx05', 'FrozenObservationControls'),
                                ('rx09', 'FrozenObservationControls')]:
            report = directory / (control + '.json')
            source = root / 'CasAcceptance/Kernel' / (module + '.lean')
            guards.append(record(source))
            environment = (['CAS_FROZEN_LEAF_MANIFEST=' + str(manifest),
                            'CAS_FIXED_QUESTION_REPORT=' + str(report),
                            'CAS_CONDITION_PROTOCOL_DIR=' + str(root / 'CasAcceptance/Strata')]
                           if control == 'rx10' else
                           ['CAS_EXTENSION_CONTROL=' + control.upper(),
                            'CAS_EXTENSION_CONTROL_REPORT=' + str(report)])
            command = ['env', *environment, 'bash', str(runtime / 'lake.sh'),
                       'env', 'lean', str(source)]
            invocations.append((control, report, command, None))
    else:
        exported = runtime / 'evidence/pure-questions'
        summary = exported / 'summary.json'
        receipt = json.loads(summary.read_text())
        if receipt.get('completeExports') is not True or receipt.get('producer') != gate['producer'] \
                or receipt.get('publishedKernel') != published:
            raise SystemExit('Fixed execution requires the complete exports from this exact built source')
        guards += [record(summary), *receipt['sourceInputs']]
        suite, inventory = exported / 'positive-clarified', exported / 'fixed-inventory.json'
        fixture = json.loads((root / 'scripts/probes/fixed_question_export_inputs.json').read_text())
        files = sorted(suite.glob('*.cas'))
        expected = question_sources(files)
        if len(files) != 14 or len(expected) != 134 \
                or set(expected) != set(fixture['assertions']) \
                or json.loads(inventory.read_text()) != {'assertions': fixture['assertions']}:
            raise SystemExit('Fixed execution selection differs from the original 134 questions in 14 files')
        for item in fixture['extensionSources']:
            path = suite / item['selectedName']
            if record(path)['sha256'] != item['sha256']:
                raise SystemExit('Staged fixed source changed: ' + str(path))
        guards += [record(inventory), *[record(path) for path in files]]
        report = directory / 'fixed-positive.json'
        command = ['bash', str(runtime / 'lake.sh'), 'env',
                   str(root / '.lake/build/bin/cas-harness'), '--suite', str(suite),
                   '--inventory', str(inventory), '--manifest', str(manifest),
                   '--report', str(report), '--computation-only']
        for module in FIXED_IMPORTS:
            command.extend(['--import', module])
        invocations.append(('fixed-positive', report, command, expected))
    if changed_records(guards):
        raise SystemExit('A fixed execution input changed since its recorded build/export')
    results = {}
    summary_path = directory / 'summary.json'
    summary = {'purpose': 'Existing fixed computations and controls; no independent acceptance claimed',
               **gate, 'frozenLeaf': leaf, 'manifest': record(manifest), 'results': results,
               'guardedInputs': guards, 'completeExecution': False}
    write(summary_path, summary)
    for selection, report, command, expected in invocations:
        code = export_attempt(root, runtime, name + '-' + selection, command)
        problems = []
        if code != 0:
            problems.append('original runner exited unsuccessfully: ' + str(code))
        try:
            document = json.loads(report.read_text())
            problems += (check_fixed_controls(selection, document) if controls else
                         check_fixed_execution(document, expected))
        except (OSError, ValueError, KeyError, TypeError) as error:
            problems.append('fixed report unavailable or malformed: ' + str(error))
        changes = changed_records(guards)
        leaf_after = state(leaf_root)
        if changes or leaf_after != leaf:
            problems.append('fixed source, artifact, input or frozen leaf changed during execution')
        results[selection] = {'exit': code, 'problems': problems, 'complete': not problems,
                              'report': record(report) if report.is_file() else {'missing': True},
                              'changedInputs': changes, 'frozenLeafAfter': leaf_after}
        write(summary_path, summary)
        # Failed assertions do not suppress independent controls, but changed
        # inputs invalidate the frozen experiment and must not be reused.
        if changes or leaf_after != leaf:
            break
    summary['completeExecution'] = (len(results) == len(invocations)
                                    and all(item['complete'] for item in results.values()))
    write(summary_path, summary)
    if not summary['completeExecution']:
        raise SystemExit('Fixed computations or controls failed; inspect ' + str(summary_path))


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
    for name in ['export-api', 'export-questions']:
        export = commands.add_parser(name)
        export.add_argument('--published-kernel-commit', required=True,
                            help='complete published SHA of this already built candidate')
    for name in ['execute-fixed', 'execute-fixed-controls']:
        execution = commands.add_parser(name)
        execution.add_argument('--published-kernel-commit', required=True)
        execution.add_argument('--manifest', type=Path, required=True)
        execution.add_argument('--leaf-commit', required=True,
                               help='exact frozen leaf SHA shared with the original RX-LIFT run')
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
    elif args.phase == 'export-api':
        api_export(root, runtime, args.published_kernel_commit)
    elif args.phase == 'export-questions':
        questions_export(root, runtime, args.published_kernel_commit)
    elif args.phase in {'execute-fixed', 'execute-fixed-controls'}:
        fixed_execution(root, runtime, args.published_kernel_commit, args.manifest,
                        args.leaf_commit, controls=args.phase == 'execute-fixed-controls')
    else:
        verify(root, runtime)


if __name__ == '__main__':
    main()
