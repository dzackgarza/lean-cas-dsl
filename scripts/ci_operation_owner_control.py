#!/usr/bin/env python3
"""Run frozen action controls against the candidate and the f65 Realize component.

Only the published baseline Realize source is recompiled, outside every source
checkout. Both components use the identical current dependency artifacts. Only
the explicitly reviewed source pairs in REVIEWED_DEPENDENCY_SOURCES may differ
from f65; each before/after source and its delta are retained. These shared
internal APIs preserve baseline-call compatibility. This is not a historical
full-kernel baseline or mathematical acceptance.

Lean 4.33 source references for the invocation:
  src/Lean/Shell.lean: --setup, --json and -o
  src/Lean/Setup.lean: ModuleSetup and ImportArtifacts
  src/Lean/Environment.lean: writeModule and importModulesCore artifact selection
  src/lake/Lake/Build/Module.lean: computeExportInfo's ordinary/meta artifact arrays
All are at https://github.com/leanprover/lean4/tree/v4.33.0 .
"""

import argparse
from collections import Counter
import copy
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

import ci_kernel_candidate as candidate


BASELINE = 'f65f3e9bed748ee8bc699e16ff43d29fb8fbce79'
MODULE = 'CasCatalogue.Realize'
REALIZE = 'CasCatalogue/Realize.lean'
BASELINE_REALIZE_SHA256 = '79c1257296030f7be30624ea6fede5786c18d241dacb7d9c31b761e290dcc53e'
# Replace only after the source owner freezes the complete reviewed candidate,
# including the registered-product comparison. No CLI or environment override.
CANDIDATE_REALIZE_SHA256 = 'e2c1e462aa38efbf34bf6f465dd3de92d0fa912feb06a014e8cff9be27fd2f07'
REVIEWED_DEPENDENCY_SOURCES = {
    'CasCatalogue/DeclaredApplication.lean': {
        'before': None,
        'after': '4091f20608ee3f7644313c28b1434769ab8995b8dc1aaaf99a1a6cce09a40759',
        'scope': 'New shared full declaration matcher extracted from the existing Realize interface; the original wrapper delegates without changing its signature'},
    'CasCatalogue/RoutedResultPlan.lean': {
        'before': None,
        'after': 'f59380c3a108fa7213154b0b5e5bb5eb9c2013fd85109959c76b53953e75dbca',
        'scope': 'New pure declaration-derived result schema retains original parameter and public field positions; it does not dispatch or manufacture mathematical values'},
    'CasCatalogue/StructuredResult.lean': {
        'before': 'fb3b8495e4423d857b9626b2ade65b713e58de02a3e90d9ce23536a344f061e6',
        'after': '718cabc027c5a1dbcceffd7e0d326d013598d4e79e1f513916dde75d7695fdec',
        'scope': 'A defaulted apex binder is selected on the symbolic registered schema before formal binder unification; existing DataPlan construction remains compatible'},
    'CasCatalogue/ComputationalData.lean': {
        'before': 'c0cb16055ad7fa6fc6086f0fd3863965a02164b8bfe6b1dba39eb5e68fe82c84',
        'after': '41e98fe3978541d6be2d9ef19e2b33c2c955bbd508b3fd87ea6cf331a23c6598',
        'scope': 'Producer origins and scoped DataPlan bindings retain exact endpoint/projection roles; existing data-only endpoint and planned-port calls retain their defaults'},
    'CasCatalogue/ServiceRequest.lean': {
        'before': '4d1d2c5a4b11e63141b3eb10a8b1ed0650e55ab8263a42f40a5cf330017a8be3',
        'after': 'fa0f2c5560f16f6a0d1600df05b1b42fdf0cff097d6a4e0851184cf55120178c',
        'scope': 'Prepared retains optional exact endpoint operands; existing callers remain compatible'},
    'CasCatalogue/SimpleServiceRequest.lean': {
        'before': '4937a53e5de24b73f335f80c6ee37a2c60a5ca649424b95d9dbf95b99625c219',
        'after': '4180ea4ddf98607c3fd73303323e97d3ff0ea69a73a723b3936bcef6c079d07e',
        'scope': 'Existing simple preparers retain exact typed callable endpoint operands'},
    'CasCatalogue/StructuredServiceRequest.lean': {
        'before': '259d2fd6937020d8f7b5e76766bb4f651c7fcce1c74c0cb7238c103ed61e18f4',
        'after': '603924334dee68796c17c81ad061d890276597b3472de95cec39b2b840e77a71',
        'scope': 'Existing structured preparers retain exact typed callable endpoint operands'},
    'CasCatalogue/UniversalServiceRequest.lean': {
        'before': '4781b2991d976c080c47069461cac309f1dee946775a1b70a86f0548a60e04e5',
        'after': 'adc3a6ceae6f1af70f566b223fa5c5f350eda79aa92148507496576604346eb7',
        'scope': 'The unchanged public decoder and captured universal invocation share typed materialization/completion; exact endpoint operands remain retained'},
}

OWNER_ERROR = 'target-category operation dispatched before its two selected owner actions'
CONTROLS = (
    {'name': 'operation-owner', 'module': 'OperationOwnerExecutionProbes',
     'sha256': 'f1f7d1e749d0c4cf1653b8ca67b67d7f44828d5f258958a1c062ab81c7316632',
     'baselineErrors': (OWNER_ERROR, OWNER_ERROR)},
    {'name': 'operation-owner-admission', 'module': 'OperationOwnerAdmissionProbes',
     'sha256': '0bf716cc4ed13327a7906a44127520a2f9b86dc812f2be4e51c726a28172d067',
     'baselineErrors': None},
    {'name': 'action-occurrence', 'module': 'ActionOccurrenceProbes',
     'sha256': '068b85ce841d74497a3e776ae133a92d8499ba3a6c9d504f8cad0c38656f190d',
     'baselineErrors': (
         'a deferred object action replaced its captured source occurrence from the cache',
         'a deferred map action replaced its captured callable or endpoint occurrence from the cache',
         'a deferred action replaced its captured complete parameter occurrence from the cache')},
    {'name': 'nested-arrow-action', 'module': 'NestedArrowActionProbes',
     'sha256': 'b3ac533e1e844a68b834d61623b5be2f00d2848d3a1e7139681074444835b959',
     'baselineErrors': None},
    {'name': 'diagram-action', 'module': 'DiagramActionExecutionProbes',
     'sha256': '53131f04f80c14d0cd09b3ea9d9e2c76517c9dcde7a27119b158b72c02a07d47',
     'baselineErrors': None},
    {'name': 'returned-callable-endpoint', 'module': 'ReturnedCallableEndpointProbes',
     'sha256': 'ce916db68a71b0dd6e74a89a790d0682a10cf5e6a9f0e476b54ad8903d23781d',
     'baselineErrors': (
         'a returned whole callable replaced its invocation endpoints from the formal cache',)},
    {'name': 'arrow-framing-reuse', 'module': 'ArrowFramingReuseProbes',
     'sha256': '1b1722aded20bb0e7cc3bac06949de53aca7e57fe5f442c8cded1275cbe6819f',
     'baselineErrors': ()},
    {'name': 'intrinsic-occurrence', 'module': 'IntrinsicOccurrenceProbes',
     'sha256': 'a4cbfe9a6f16d397fdf18288962def069a06c2c7d6f7c37bc76e08753a506a8a',
     'baselineErrors': (
         'an intrinsic callable replaced its retained child occurrences from the cache',
         'an intrinsic callable replaced its retained child occurrences from the cache',
         'an intrinsic callable replaced its retained child occurrences from the cache',
         'an intrinsic identity failed to observe its retained object action')},
    # These later controls were fixed against 112dc2, not the f65f3e9 component
    # baseline. Run their frozen candidate requirements without inventing an
    # expected historical failure at a different source revision.
    {'name': 'construction-action-occurrence', 'module': 'ConstructionActionOccurrenceProbes',
     'sha256': '3e16971c544f5d773e0fe2f728324bc8b2ba2481d7ea0f0a7c2aa86e74bfaa3c',
     'baselineErrors': None},
    {'name': 'synthetic-endpoint-occurrence', 'module': 'SyntheticEndpointOccurrenceProbes',
     'sha256': '1532ff20aa60c6cdadd649b3b66372c13696e519df2b1fdfc5b71eef07065dc0',
     'baselineErrors': None},
    {'name': 'nested-owner-admission', 'module': 'NestedOwnerAdmissionProbes',
     'sha256': 'f6b8c53764e5887c3daec59077fc4f99decd0b539b9f5e196b9ef64a5d61d295',
     'baselineErrors': None},
    {'name': 'intrinsic-value-occurrence', 'module': 'IntrinsicValueOccurrenceProbes',
     'sha256': 'dc47e798c06928174d18ba6fdded0d365a85e288b880ee9d7a70f96e7df3a608',
     'baselineErrors': None},
    {'name': 'positioned-interface-scope', 'module': 'PositionedInterfaceScopeProbes',
     'sha256': '65b44b8692a5c30ea09dc57efed84112c4b1f72a9752f8c1d9b7e03336515bdf',
     'baselineErrors': None},
    {'name': 'routed-result-schema', 'module': 'RoutedResultSchemaProbes',
     'sha256': '4920d0079827667977a7f5a5922c1343853cd23b471db07151d83e44e263dad1',
     'baselineErrors': None},
    {'name': 'endpoint-comparison-occurrence', 'module': 'EndpointComparisonOccurrenceProbes',
     'sha256': '562c54a9f24527ce5f3bf5f06c8d1a0dce13dd72b0f018db18a6e20f364d952b',
     'baselineErrors': None},
)
FIXTURES = ('probe_owned_callable.py', 'probe_functor_execution.py',
            'probe_registration.py', 'probe_reply_conditions.py')
ADMISSION_CONFIGURATIONS = tuple('operation-owner-admission-' + name + '.json'
                                for name in ['portable', 'ambiguous', 'foreign', 'owned-output'])


def git_bytes(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def require_hash(data, expected, label):
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError(label + ' has no reviewed frozen SHA256; publication/control is blocked')
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(label + ' differs from its reviewed frozen SHA256')


def reviewed_source_pair(root, relative, pair):
    if pair['before'] is None:
        if git_bytes(root, 'ls-tree', '-z', BASELINE, '--', relative):
            raise ValueError('A reviewed new dependency already exists at f65: ' + relative)
        before = b''
    else:
        before = git_bytes(root, 'show', BASELINE + ':' + relative)
        require_hash(before, pair['before'], 'Published dependency ' + relative)
    after = (root / relative).read_bytes()
    require_hash(after, pair['after'], 'Reviewed dependency ' + relative)
    return before, after


def kernel_dependency_source(root, module):
    source = root / (module.replace('.', '/') + '.lean')
    if not source.is_file():
        return None
    relative = source.relative_to(root).as_posix()
    if relative in REVIEWED_DEPENDENCY_SOURCES:
        reviewed_source_pair(root, relative, REVIEWED_DEPENDENCY_SOURCES[relative])
    elif git_bytes(root, 'show', BASELINE + ':' + relative) != source.read_bytes():
        raise ValueError('An unapproved kernel dependency changed since f65: ' + relative)
    return candidate.record(source)


def import_artifacts(olean):
    """The standard, non-import-all module shape from Lake.computeExportInfo."""
    parts = [[olean, Path(str(olean) + '.server')],
             [olean.with_suffix('.ir.sig'), olean.with_suffix('.ir')]]
    if any(not path.is_file() for group in parts for path in group):
        raise ValueError('Missing compiled module or executable IR parts: ' + str(olean))
    return [[str(path.resolve()) for path in group] for group in parts]


def diagnostics(log):
    result = []
    for line in log.read_text().splitlines():
        if not line.strip():
            continue
        item = json.loads(line)
        if not isinstance(item, dict) or item.get('severity') not in {
                'information', 'warning', 'error'} or not isinstance(item.get('data'), str) \
                or not isinstance(item.get('fileName'), str):
            raise ValueError('Unexpected non-diagnostic output in ' + str(log))
        result.append(item)
    return result


def check_diagnostics(messages, code, probe, expected_errors=()):
    """Require success, or exactly the frozen execution assertions at this source."""
    errors = [item for item in messages if item['severity'] == 'error']
    if not expected_errors:
        return type(code) is int and code == 0 and not errors
    return (type(code) is int and code == 1
            and Counter(item['data'] for item in errors) == Counter(expected_errors)
            and all(Path(item['fileName']).resolve() == probe.resolve() for item in errors))


def probe_setup(directory, name, control, setup, parts, guards):
    value = copy.deepcopy(setup)
    value['name'] = 'CasAcceptance.Kernel.' + control['module']
    value['importArts'][MODULE] = parts
    path = directory / (name + '.setup.json')
    candidate.write(path, value)
    guards.append(candidate.record(path))
    return path


def execute_controls(lean, setup, directory, modules, probes, current_parts,
                     baseline_source, baseline_setup, step, guards, report):
    """All independent candidate checks run; a bad baseline compile proves nothing."""
    successful = True
    for control in probes:
        name = control['name'] + '-candidate'
        selected = probe_setup(directory, name, control, setup, current_parts, guards)
        passed = step(name, [*lean, '--setup=' + str(selected), str(control['copy'])],
                      control['copy'])
        successful = passed and successful
    baseline_olean = modules / 'CasCatalogue/Realize.olean'
    baseline_olean.parent.mkdir(parents=True)
    if not step('operation-owner-baseline-compile',
                [*lean, '--setup=' + str(baseline_setup), '-o', str(baseline_olean),
                 str(baseline_source)], baseline_source):
        report['baselineProbeDisposition'] = 'Not run: baseline component compilation failed'
        return False
    baseline_parts = import_artifacts(baseline_olean)
    produced = [candidate.record(path) for group in baseline_parts for path in group]
    private = Path(str(baseline_olean) + '.private')
    if private.is_file():
        produced.append(candidate.record(private))
    report['baselineArtifacts'] = produced
    guards.extend(produced)
    for control in probes:
        if control['baselineErrors'] is None:
            continue
        name = control['name'] + '-baseline'
        selected = probe_setup(directory, name, control, setup, baseline_parts, guards)
        passed = step(name, [*lean, '--setup=' + str(selected), str(control['copy'])],
                      control['copy'], control['baselineErrors'])
        successful = passed and successful
    return successful


def run(root, runtime, published):
    evidence = runtime / 'evidence'
    directory = evidence / 'operation-owner-control'
    modules = runtime / 'operation-owner-control-modules'
    if directory.exists() or modules.exists():
        raise ValueError('Refuse to replace earlier action-control evidence or artifacts')
    # The same already-built combination and original reader preflight gate the
    # independent pure exports and these later computational controls.
    gate = candidate.export_gate(root, runtime, published)
    producer = gate['producer']
    if Path(producer['kernel']['path']).resolve() != root:
        raise ValueError('The invocation root differs from the built kernel checkout')
    if producer != json.loads((evidence / 'source-tuple-before.json').read_text()):
        raise ValueError('Action controls require the unchanged original candidate tuple')
    if any(runtime.is_relative_to(Path(item['path']).resolve()) for item in producer.values()):
        raise ValueError('Control sources and artifacts must be outside selected source trees')
    guards = [*gate['guardedInputs'], candidate.record(__file__)]
    pure_exports = {}
    for folder, complete in [('public-api', 'completeExport'), ('pure-questions', 'completeExports')]:
        path = evidence / folder / 'summary.json'
        receipt = json.loads(path.read_text())
        if receipt.get(complete) is not True or receipt.get('producer') != producer \
                or receipt.get('publishedKernel') != published:
            raise ValueError('Matching completed pure export is required first: ' + folder)
        pure_exports[folder] = candidate.record(path)
        guards.append(pure_exports[folder])
    builds = {}
    for name in ['consumers', 'native', 'axiom-audit']:
        path = evidence / (name + '-provenance.json')
        receipt = json.loads(path.read_text())
        if receipt.get('status') != 'completed' or receipt.get('exit') != 0 \
                or receipt.get('sourceTupleChanged') is not False \
                or receipt.get('producer') != producer or receipt.get('producerAfter') != producer:
            raise ValueError('A matching successful ' + name + ' build receipt is required')
        builds[name] = candidate.record(path)
        guards += [builds[name], receipt['log']]
    if candidate.git(root, 'rev-parse', BASELINE + '^{commit}') != BASELINE:
        raise ValueError('The exact published baseline is unavailable')
    for name in ['lake-manifest.json', 'lean-toolchain']:
        if git_bytes(root, 'show', BASELINE + ':' + name) != (root / name).read_bytes():
            raise ValueError('Baseline and candidate select different dependencies/toolchain: ' + name)
    baseline_bytes = git_bytes(root, 'show', BASELINE + ':' + REALIZE)
    require_hash(baseline_bytes, BASELINE_REALIZE_SHA256, 'Published f65 Realize source')
    require_hash((root / REALIZE).read_bytes(), CANDIDATE_REALIZE_SHA256, 'Candidate Realize source')
    reviewed_sources = {}
    for relative, pair in REVIEWED_DEPENDENCY_SOURCES.items():
        reviewed_sources[relative] = reviewed_source_pair(root, relative, pair)

    setup_path = root / '.lake/build/ir/CasCatalogue/Realize.setup.json'
    setup = json.loads(setup_path.read_text())
    reviewed_modules = {path.removesuffix('.lean').replace('/', '.') for path in reviewed_sources}
    if setup.get('name') != MODULE or setup.get('isModule') is not True \
            or setup.get('imports') is not None or not isinstance(setup.get('importArts'), dict) \
            or not setup['importArts'] or MODULE in setup['importArts'] \
            or not reviewed_modules.issubset(setup['importArts']):
        raise ValueError('Expected the original complete Realize dependency setup without a header override')
    guards += [candidate.record(setup_path), candidate.record(root / REALIZE)]
    # Every import artifact is shared by both components. All kernel dependency
    # sources outside the exact hash-authenticated reviewed pairs remain
    # byte-identical to f65. Never use a partial directory LEAN_PATH overlay.
    dependency_paths = set()
    kernel_dependencies = []
    for module, groups in setup['importArts'].items():
        for group in groups:
            for value in group:
                dependency_paths.add((root / value).resolve())
        source = kernel_dependency_source(root, module)
        if source is not None:
            kernel_dependencies.append(source)
    for value in setup.get('dynlibs', []):
        dependency_paths.add((root / value).resolve())
    for plugin in setup.get('plugins', []):
        dependency_paths.add((root / plugin['path']).resolve())
    dependency_artifacts = [candidate.record(path) for path in sorted(dependency_paths)]
    current_olean = root / '.lake/build/lib/lean/CasCatalogue/Realize.olean'
    current_parts = import_artifacts(current_olean)
    own_artifacts = [candidate.record(path) for group in current_parts for path in group]
    private = Path(str(current_olean) + '.private')
    if private.is_file():
        own_artifacts.append(candidate.record(private))
    probes = []
    for control in CONTROLS:
        source = root / 'CasAcceptance/Kernel' / (control['module'] + '.lean')
        require_hash(source.read_bytes(), control['sha256'], 'Frozen ' + control['module'])
        item = candidate.record(source)
        probes.append({**control, 'original': item})
        guards.append(item)
    contract = Path(producer['contract']['path'])
    guards += [*dependency_artifacts, *kernel_dependencies, *own_artifacts,
               candidate.record(contract / 'python/cas_port.py'),
               *[candidate.record(root / 'CasAcceptance/Strata' / name) for name in FIXTURES]]
    changes = candidate.changed_records(guards)
    if changes:
        raise ValueError('Control inputs changed after their recorded build: ' + ', '.join(changes))

    directory.mkdir()
    modules.mkdir()
    admission_runtime = directory / 'admission-configurations'
    admission_runtime.mkdir()
    baseline_source = directory / 'baseline-source' / REALIZE
    baseline_source.parent.mkdir(parents=True)
    baseline_source.write_bytes(baseline_bytes)
    current_source = directory / 'candidate-source' / REALIZE
    current_source.parent.mkdir(parents=True)
    current_source.write_bytes((root / REALIZE).read_bytes())
    deltas = []
    for relative, (original, current) in reviewed_sources.items():
        before = directory / 'baseline-source' / relative
        after = directory / 'candidate-source' / relative
        before.parent.mkdir(parents=True, exist_ok=True)
        after.parent.mkdir(parents=True, exist_ok=True)
        before.write_bytes(original)
        after.write_bytes(current)
        delta = directory / 'reviewed-dependency-deltas' / Path(relative).with_suffix('.patch')
        delta.parent.mkdir(parents=True, exist_ok=True)
        delta.write_text(''.join(difflib.unified_diff(
            original.decode().splitlines(keepends=True), current.decode().splitlines(keepends=True),
            fromfile='f65/' + relative, tofile='candidate/' + relative)))
        deltas.append({
            'path': relative, 'baselineBlob': (
                candidate.git(root, 'rev-parse', BASELINE + ':' + relative)
                if REVIEWED_DEPENDENCY_SOURCES[relative]['before'] is not None else None),
            'newDependency': REVIEWED_DEPENDENCY_SOURCES[relative]['before'] is None,
            'before': candidate.record(before), 'after': candidate.record(after),
            'patch': candidate.record(delta), 'scope': REVIEWED_DEPENDENCY_SOURCES[relative]['scope']})
        guards += [candidate.record(path) for path in [before, after, delta]]
    baseline_setup = directory / 'baseline-realize.setup.json'
    baseline_setup.write_bytes(setup_path.read_bytes())
    for control in probes:
        path = directory / 'probes/CasAcceptance/Kernel' / (control['module'] + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(Path(control['original']['path']).read_bytes())
        control['copy'] = path
        guards.append(candidate.record(path))
    guards += [candidate.record(path) for path in
               [baseline_source, current_source, baseline_setup]]
    environment = ['env', 'PYTHONDONTWRITEBYTECODE=1',
                   'CAS_OWNERSHIP_PROTOCOL_DIR=' + str(root / 'CasAcceptance/Strata'),
                   'CAS_OWNER_ADMISSION_RUNTIME_DIR=' + str(admission_runtime),
                   'CAS_LEAF_CONTRACT_PATH=' + str(contract),
                   'PYTHONPATH=' + str(contract / 'python')]
    lean = [*environment, 'bash', str(runtime / 'lake.sh'), 'env', 'lean', '--json']
    report = {
        'purpose': 'Frozen action execution engineering controls; no mathematical or architectural acceptance',
        **gate, 'verifiedBuilds': builds, 'priorPureExports': pure_exports,
        'baselineDescription': 'f65 Realize component baseline with shared current dependencies',
        'baselineKernelSourceCommit': BASELINE,
        'baselineBlob': candidate.git(root, 'rev-parse', BASELINE + ':' + REALIZE),
        'baselineSource': candidate.record(baseline_source),
        'candidateSource': candidate.record(current_source), 'candidateArtifacts': own_artifacts,
        'sharedDependencySetup': candidate.record(baseline_setup),
        'sharedDependencyArtifacts': dependency_artifacts,
        'sharedKernelDependencySources': kernel_dependencies,
        'reviewedCompatibilityDeltas': deltas,
        'controls': [{**{key: value for key, value in control.items() if key != 'copy'},
                      'executedSourceCopy': candidate.record(control['copy']),
                      'baselineExpected': ('not run' if control['baselineErrors'] is None else
                                           'exact assertion errors' if control['baselineErrors'] else 'success')}
                     for control in probes],
        'admissionRuntime': str(admission_runtime),
        'startedUtc': candidate.stamp(), 'status': 'running', 'steps': {},
        'guardedInputs': guards,
    }
    report_path = directory / 'summary.json'
    candidate.write(report_path, report)
    start = time.monotonic()
    code = 1

    def step(name, command, source, expected_errors=()):
        path = evidence / (name + '-provenance.json')
        if path.exists() or (evidence / (name + '.log')).exists():
            raise ValueError('Refuse to reuse an earlier control invocation: ' + name)
        try:
            candidate.run(root, runtime, name, command)
        except SystemExit:
            pass  # Inspect the full receipt and exact diagnostics, including red controls.
        receipt = json.loads(path.read_text())
        if receipt.get('status') != 'completed' or receipt.get('producer') != producer \
                or receipt.get('producerAfter') != producer or receipt.get('sourceTupleChanged') is not False \
                or receipt.get('command') != command:
            raise ValueError('Control invocation did not complete with stable sources: ' + name)
        if candidate.record(receipt['log']['path']) != receipt['log']:
            raise ValueError('Control log changed: ' + name)
        messages = diagnostics(Path(receipt['log']['path']))
        valid = check_diagnostics(messages, receipt['exit'], source, expected_errors)
        report['steps'][name] = {
            'invocation': candidate.record(path), 'diagnostics': messages,
            'exit': receipt['exit'], 'expectedErrors': list(expected_errors),
            'expectedResultObserved': valid}
        guards.extend([candidate.record(path), receipt['log']])
        candidate.write(report_path, report)
        if name == 'operation-owner-admission-candidate':
            configurations = sorted(admission_runtime.iterdir())
            for configuration in configurations:
                if configuration.name not in ADMISSION_CONFIGURATIONS or not configuration.is_file() \
                        or not isinstance(json.loads(configuration.read_text()), dict):
                    raise ValueError('Unexpected generated admission configuration: ' + str(configuration))
            records = [candidate.record(configuration) for configuration in configurations]
            report['admissionConfigurations'] = records
            guards.extend(records)
            if valid and {path.name for path in configurations} != set(ADMISSION_CONFIGURATIONS):
                raise ValueError('Successful admission control omitted its four retained configurations')
            candidate.write(report_path, report)
        changes = candidate.changed_records(guards)
        if changes:
            raise ValueError('Immutable control input/output changed: ' + ', '.join(changes))
        return valid

    try:
        if execute_controls(lean, setup, directory, modules, probes, current_parts,
                            baseline_source, baseline_setup, step, guards, report):
            code = 0
        else:
            report['error'] = 'One or more controls did not reach their exact required result'
    except (Exception, SystemExit) as error:
        report['error'] = repr(error)
    finally:
        after_state = candidate.snapshot(runtime)
        changes = candidate.changed_records(guards)
        if after_state != producer or changes:
            code = 2
        report.update(status='completed', exit=code, finishedUtc=candidate.stamp(),
                      seconds=round(time.monotonic() - start, 3), producerAfter=after_state,
                      sourceTupleChanged=after_state != producer, changedInputs=changes,
                      guardedInputs=guards, completeEngineeringControl=code == 0)
        candidate.write(report_path, report)
    print(json.dumps({'report': str(report_path), 'exit': code, 'error': report.get('error')}), flush=True)
    return code


def self_test():
    """Exercise error classification and invocation/overlay isolation without Lean."""
    import tempfile
    import unittest
    from unittest.mock import Mock, patch

    class DiagnosticTests(unittest.TestCase):
        def setUp(self):
            self.temp = tempfile.TemporaryDirectory()
            self.addCleanup(self.temp.cleanup)
            self.root = Path(self.temp.name)
            self.source = self.root / 'original.lean'

        def message(self, text, **fields):
            return {'severity': 'error', 'fileName': str(self.source), 'data': text, **fields}

        def test_exact_named_errors_and_counts(self):
            for expected in [item['baselineErrors'] for item in CONTROLS if item['baselineErrors']]:
                messages = [self.message(text) for text in expected]
                self.assertTrue(check_diagnostics(list(reversed(messages)), 1, self.source, expected))
                for invalid in [messages[:-1], messages + messages[:1],
                                [*messages[:-1], self.message('type mismatch')],
                                [*messages[:-1], self.message(expected[-1] + ' (other error)')]]:
                    self.assertFalse(check_diagnostics(invalid, 1, self.source, expected))
                self.assertFalse(check_diagnostics(
                    [self.message(text, fileName=str(self.root / 'dependency.lean')) for text in expected],
                    1, self.source, expected))
                for code in [0, 2, -9, True, '1']:
                    self.assertFalse(check_diagnostics(messages, code, self.source, expected))

        def test_success_requires_zero_and_no_errors(self):
            self.assertTrue(check_diagnostics([], 0, self.source))
            self.assertTrue(check_diagnostics([self.message('note', severity='information')], 0, self.source))
            self.assertFalse(check_diagnostics([self.message(OWNER_ERROR)], 0, self.source))
            self.assertFalse(check_diagnostics([], 1, self.source))
            self.assertFalse(check_diagnostics([], False, self.source))

        def test_json_parser_rejects_unframed_or_malformed_output(self):
            log = self.root / 'lean.log'
            expected = self.message(OWNER_ERROR)
            log.write_text('\n' + json.dumps(expected) + '\n\n')
            self.assertEqual(diagnostics(log), [expected])
            for text in ['runtime crash\n', '{}\n', '[]\n',
                         json.dumps({**expected, 'severity': 'fatal'}),
                         json.dumps({**expected, 'fileName': None}),
                         json.dumps({**expected, 'data': ['not a diagnostic']})]:
                log.write_text(text)
                with self.assertRaises(ValueError):
                    diagnostics(log)

        def test_pending_and_mismatched_source_pins_block(self):
            digest = hashlib.sha256(b'original').hexdigest()
            require_hash(b'original', digest, 'fixture')
            with self.assertRaisesRegex(ValueError, 'no reviewed frozen SHA256'):
                require_hash(b'original', 'PENDING_REVIEW', 'fixture')
            with self.assertRaisesRegex(ValueError, 'differs'):
                require_hash(b'changed', digest, 'fixture')

        def test_only_the_exact_reviewed_dependency_sources_may_change(self):
            import sys
            this = sys.modules[__name__]
            other = self.root / 'CasCatalogue/Other.lean'
            other.parent.mkdir()
            other.write_bytes(b'changed')
            self.assertEqual(set(REVIEWED_DEPENDENCY_SOURCES), {
                'CasCatalogue/ComputationalData.lean', 'CasCatalogue/ServiceRequest.lean',
                'CasCatalogue/SimpleServiceRequest.lean', 'CasCatalogue/StructuredServiceRequest.lean',
                'CasCatalogue/UniversalServiceRequest.lean', 'CasCatalogue/StructuredResult.lean',
                'CasCatalogue/DeclaredApplication.lean', 'CasCatalogue/RoutedResultPlan.lean'})
            before = hashlib.sha256(b'baseline').hexdigest()
            reviewed = {}
            for relative in REVIEWED_DEPENDENCY_SOURCES:
                source = self.root / relative
                source.write_text('reviewed change in ' + relative)
                reviewed[relative] = {'before': before, 'after': candidate.record(source)['sha256']}
            with patch.object(this, 'git_bytes', return_value=b'baseline'), \
                    patch.object(this, 'REVIEWED_DEPENDENCY_SOURCES', reviewed):
                for relative in reviewed:
                    module = relative.removesuffix('.lean').replace('/', '.')
                    self.assertEqual(kernel_dependency_source(self.root, module),
                                     candidate.record(self.root / relative))
                with self.assertRaisesRegex(ValueError, 'unapproved kernel dependency'):
                    kernel_dependency_source(self.root, 'CasCatalogue.Other')
                other.write_bytes(b'baseline')
                self.assertEqual(kernel_dependency_source(self.root, 'CasCatalogue.Other'),
                                 candidate.record(other))
                helper = self.root / 'CasCatalogue/ComputationalData.lean'
                helper.write_bytes(b'an additional unreviewed change')
                with self.assertRaisesRegex(ValueError, 'reviewed frozen SHA256'):
                    kernel_dependency_source(self.root, 'CasCatalogue.ComputationalData')
                reviewed['CasCatalogue/ServiceRequest.lean']['after'] = 'PENDING_REVIEW'
                with self.assertRaisesRegex(ValueError, 'no reviewed frozen SHA256'):
                    kernel_dependency_source(self.root, 'CasCatalogue.ServiceRequest')

        def test_new_dependency_requires_absence_and_its_exact_reviewed_bytes(self):
            import sys
            this = sys.modules[__name__]
            source = self.root / 'New.lean'
            source.write_bytes(b'new module')
            pair = {'before': None, 'after': candidate.record(source)['sha256']}
            with patch.object(this, 'git_bytes', return_value=b''):
                self.assertEqual(reviewed_source_pair(self.root, 'New.lean', pair),
                                 (b'', b'new module'))
                source.write_bytes(b'changed module')
                with self.assertRaisesRegex(ValueError, 'reviewed frozen SHA256'):
                    reviewed_source_pair(self.root, 'New.lean', pair)
            with patch.object(this, 'git_bytes', return_value=b'existing tree entry'):
                with self.assertRaisesRegex(ValueError, 'already exists at f65'):
                    reviewed_source_pair(self.root, 'New.lean', pair)

        def test_all_declared_probe_bytes_are_frozen(self):
            root = Path(__file__).resolve().parents[1]
            self.assertEqual([item['module'] for item in CONTROLS], [
                'OperationOwnerExecutionProbes', 'OperationOwnerAdmissionProbes', 'ActionOccurrenceProbes',
                'NestedArrowActionProbes', 'DiagramActionExecutionProbes',
                'ReturnedCallableEndpointProbes', 'ArrowFramingReuseProbes',
                'IntrinsicOccurrenceProbes', 'ConstructionActionOccurrenceProbes',
                'SyntheticEndpointOccurrenceProbes', 'NestedOwnerAdmissionProbes',
                'IntrinsicValueOccurrenceProbes', 'PositionedInterfaceScopeProbes',
                'RoutedResultSchemaProbes',
                'EndpointComparisonOccurrenceProbes'])
            for control in CONTROLS:
                source = root / 'CasAcceptance/Kernel' / (control['module'] + '.lean')
                require_hash(source.read_bytes(), control['sha256'], control['module'])

    class InvocationTests(unittest.TestCase):
        def setUp(self):
            self.temp = tempfile.TemporaryDirectory()
            self.addCleanup(self.temp.cleanup)
            self.root = Path(self.temp.name)
            self.directory = self.root / 'evidence'
            self.directory.mkdir()
            self.modules = self.root / 'baseline-modules'
            self.setup = {'name': MODULE, 'isModule': True, 'importArts': {
                'CasCatalogue.ComputationalData': [['current-dependency.olean'], ['current-dependency.ir']],
                'Lean': [['shared-lean.olean'], []]}, 'options': {'retain': 'original'}}
            self.setup_original = copy.deepcopy(self.setup)
            self.baseline_source = self.root / 'original-Realize.lean'
            self.baseline_source.write_bytes(b'unchanged original baseline source\n')
            self.baseline_setup = self.root / 'original.setup.json'
            candidate.write(self.baseline_setup, self.setup)
            self.current_parts = [['candidate.olean', 'candidate.olean.server'],
                                  ['candidate.ir.sig', 'candidate.ir']]
            self.probes = []
            for control in CONTROLS:
                source = self.root / (control['module'] + '.lean')
                source.write_text(control['module'] + ': immutable source fixture\n')
                self.probes.append({**control, 'copy': source})
            self.guards = [candidate.record(self.baseline_source), candidate.record(self.baseline_setup)]
            self.guards += [candidate.record(control['copy']) for control in self.probes]
            self.report = {}

        def execute(self, failures=(), omit_artifacts=False):
            def invoke(name, command, source, expected_errors=()):
                self.assertEqual(command[-1], str(source))
                self.assertFalse(any('heartbeats' in value or 'maxRecDepth' in value for value in command))
                self.assertTrue(str(source).startswith(str(self.root)))
                if name == 'operation-owner-baseline-compile' and name not in failures and not omit_artifacts:
                    olean = Path(command[command.index('-o') + 1])
                    for path in [olean, Path(str(olean) + '.server'),
                                 olean.with_suffix('.ir.sig'), olean.with_suffix('.ir'),
                                 Path(str(olean) + '.private')]:
                        path.write_bytes(b'separate compiled component fixture\n')
                return name not in failures
            self.step = Mock(side_effect=invoke)
            return execute_controls(['lean', '--json'], self.setup, self.directory, self.modules,
                                    self.probes, self.current_parts, self.baseline_source,
                                    self.baseline_setup, self.step, self.guards, self.report)

        def test_exact_candidate_and_baseline_matrix_and_shared_artifacts(self):
            self.assertTrue(self.execute())
            names = [call.args[0] for call in self.step.call_args_list]
            self.assertEqual(names, [
                'operation-owner-candidate', 'operation-owner-admission-candidate', 'action-occurrence-candidate',
                'nested-arrow-action-candidate', 'diagram-action-candidate',
                'returned-callable-endpoint-candidate', 'arrow-framing-reuse-candidate',
                'intrinsic-occurrence-candidate',
                'construction-action-occurrence-candidate', 'synthetic-endpoint-occurrence-candidate',
                'nested-owner-admission-candidate', 'intrinsic-value-occurrence-candidate',
                'positioned-interface-scope-candidate',
                'routed-result-schema-candidate',
                'endpoint-comparison-occurrence-candidate',
                'operation-owner-baseline-compile', 'operation-owner-baseline',
                'action-occurrence-baseline', 'returned-callable-endpoint-baseline',
                'arrow-framing-reuse-baseline', 'intrinsic-occurrence-baseline'])
            self.assertEqual(self.setup, self.setup_original)
            baseline_parts = import_artifacts(self.modules / 'CasCatalogue/Realize.olean')
            for call in self.step.call_args_list:
                name, command, source, *expected = call.args
                if name == 'operation-owner-baseline-compile':
                    self.assertEqual(json.loads(self.baseline_setup.read_text()), self.setup_original)
                    self.assertEqual(source, self.baseline_source)
                    self.assertFalse(expected)
                    continue
                selected = json.loads(Path(next(value.split('=', 1)[1] for value in command
                                                if value.startswith('--setup='))).read_text())
                parts = selected['importArts'].pop(MODULE)
                self.assertEqual(selected['importArts'], self.setup_original['importArts'])
                self.assertEqual(selected['options'], self.setup_original['options'])
                self.assertEqual(parts, self.current_parts if name.endswith('-candidate') else baseline_parts)
                self.assertEqual(selected['name'], 'CasAcceptance.Kernel.' + source.stem)
                self.assertNotIn('-o', command)
            baseline_calls = self.step.call_args_list[-5:]
            self.assertEqual(baseline_calls[0].args[3], (OWNER_ERROR, OWNER_ERROR))
            self.assertEqual(len(baseline_calls[1].args[3]), 3)
            self.assertEqual(len(set(baseline_calls[1].args[3])), 3)
            self.assertEqual(baseline_calls[2].args[3], (
                'a returned whole callable replaced its invocation endpoints from the formal cache',))
            self.assertEqual(baseline_calls[3].args[3], ())
            self.assertEqual(Counter(baseline_calls[4].args[3]), Counter({
                'an intrinsic callable replaced its retained child occurrences from the cache': 3,
                'an intrinsic identity failed to observe its retained object action': 1}))
            self.assertEqual(candidate.changed_records(self.guards), [])
            self.assertEqual(len(self.report['baselineArtifacts']), 5)

        def test_unrelated_baseline_compile_failure_is_never_an_expected_red_control(self):
            self.assertFalse(self.execute(failures={'operation-owner-baseline-compile'}))
            self.assertEqual(len(self.step.call_args_list), len(CONTROLS) + 1)
            self.assertIn('compilation failed', self.report['baselineProbeDisposition'])
            self.assertNotIn('baselineArtifacts', self.report)

        def test_zero_compile_exit_without_artifacts_cannot_pass(self):
            with self.assertRaisesRegex(ValueError, 'Missing compiled module'):
                self.execute(omit_artifacts=True)
            self.assertEqual(len(self.step.call_args_list), len(CONTROLS) + 1)

        def test_a_failed_candidate_does_not_suppress_other_independent_controls(self):
            self.assertFalse(self.execute(failures={'operation-owner-candidate'}))
            self.assertEqual(len(self.step.call_args_list), 21)

        def test_the_baseline_framing_control_must_pass(self):
            self.assertFalse(self.execute(failures={'arrow-framing-reuse-baseline'}))
            framing = next(call for call in self.step.call_args_list
                           if call.args[0] == 'arrow-framing-reuse-baseline')
            self.assertEqual(framing.args[3], ())

        def test_generated_setups_and_compiled_parts_are_guarded(self):
            self.assertTrue(self.execute())
            setup = self.directory / 'action-occurrence-baseline.setup.json'
            original = candidate.record(setup)
            self.assertIn(original, self.guards)
            setup.write_text('{}\n')
            private = self.modules / 'CasCatalogue/Realize.olean.private'
            private.write_bytes(b'mutated artifact')
            self.assertEqual(set(candidate.changed_records(self.guards)), {str(setup), str(private)})

    suite = unittest.TestSuite([
        unittest.defaultTestLoader.loadTestsFromTestCase(DiagnosticTests),
        unittest.defaultTestLoader.loadTestsFromTestCase(InvocationTests)])
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--runtime', type=Path,
                        default=Path(os.environ.get('RUNNER_TEMP', '/tmp')) / 'kernel-v1-candidate')
    parser.add_argument('--published-kernel-commit', default=os.environ.get('GITHUB_SHA'))
    parser.add_argument('--self-test', action='store_true', help='Run mocked parser/orchestration controls without Lean')
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    if not args.published_kernel_commit:
        parser.error('--published-kernel-commit is required outside the published Actions checkout')
    return run(args.root.resolve(), args.runtime.resolve(), args.published_kernel_commit)


if __name__ == '__main__':
    raise SystemExit(main())
