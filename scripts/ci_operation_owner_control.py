#!/usr/bin/env python3
"""Run frozen controls against the candidate and the exact f65 kernel closure.

The historical kernel is extracted byte-for-byte from its published git tree and
built in an isolated runtime checkout with its own internal import closure. It
never imports a candidate Trace, Semantic, or other kernel module. Both builds
use the selected external semantic/toolchain tuple; only an exact reviewed
compatible contract revision may differ from f65's manifest. Candidate source
pairs remain hash guarded, but they no longer claim historical ABI compatibility.
These are engineering controls, not independent mathematical acceptance.

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
import io
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tarfile
import time

import ci_kernel_candidate as candidate


BASELINE = 'f65f3e9bed748ee8bc699e16ff43d29fb8fbce79'
MODULE = 'CasCatalogue.Realize'
REALIZE = 'CasCatalogue/Realize.lean'
BASELINE_REALIZE_SHA256 = '79c1257296030f7be30624ea6fede5786c18d241dacb7d9c31b761e290dcc53e'
# Replace only after the source owner freezes the complete reviewed candidate,
# including the registered-product comparison. No CLI or environment override.
CANDIDATE_REALIZE_SHA256 = '17551055b02f219a97137b48d7ff07604d45a67ae2312da3d887abf3867f9bfa'
REVIEWED_DEPENDENCY_SOURCES = {
    'CasCatalogue/ObjectPresentation.lean': {
        'before': '7ae808d09cce776c4eab6d18a022851ffd8da4ae4366c2059d728457ac320ebf',
        'after': '952b500c2c432d74bcd11281614f37efc8f2e2f9a210dad4426964fbd0c447a7',
        'scope': 'Public named-refinement fields project the accepted identification in its complete target category and return addressed producer occurrences'},
    'CasCatalogue/FunctorActionData.lean': {
        'before': '5940b628eac528839948ed947b62a613bab97e46966a8be295d580ab4e59dfc6',
        'after': 'f84b204f539bf2a676d42d21ebac77e8dc7e039706c002bcadb9778a2d10e64c',
        'scope': 'Literal action inspection passes through administrative producer wrappers while retaining original selected typed operands'},
    'CasCatalogue/StructuredProjection.lean': {
        'before': 'b0b5687201fcbc2033aedc7252ac42eadf2ad8de25ceb9b952dd85b89947e374',
        'after': '2e28e275fb8e7a638de11bfd19a6ae0a2cfb6fc3761fa05ea30959731e884107',
        'scope': 'Universal interface recovery inspects the original anchored value and preserves any existing producer instead of overwriting it'},
    'CasCatalogue/DeclaredApplication.lean': {
        'before': None,
        'after': 'a87eff6d63fa068817b2175cb8fc7bcda634138fc06b29cc583618e9df85f4f4',
        'scope': 'New shared full declaration matcher extracted from the existing Realize interface; the original wrapper delegates without changing its signature'},
    'CasCatalogue/RoutedResultPlan.lean': {
        'before': None,
        'after': 'f90bc2b292606dba9fa6fc9cfe343c5c49ab1a98eb226f0b06f898f0a101a9d2',
        'scope': 'Dependent result schemas retain symbolic parameter origins, exact public field positions, comparison-aligned projection actions and final reply paths across composition; no mathematical values are manufactured'},
    'CasCatalogue/LiftStageExecution.lean': {
        'before': None,
        'after': '4cef385c924dc50f0bf951d211ce242e884a2abf17deec49322468eae21f1995',
        'scope': 'Shared four-field dependency fold over retained operands; actual and prospective lift consumers supply their existing image and field callbacks without changing legacy packet order'},
    'CasCatalogue/Language.lean': {
        'before': '585a2e71efec55c1164726f528a5d1f3cb3bd23052a74f48e080a3c0164769a1',
        'after': 'e57ea6c512e44925d2cc30c395607a76b75f94fd7e434b0bd4a51fa7396e779f',
        'scope': 'Complete source contexts and dependent typed selection for object/map parameters, numeral owners, registered tuple construction and exact oriented limit choices; no new mathematical objects or operations'},
    'CasCatalogue/StructuredResult.lean': {
        'before': 'fb3b8495e4423d857b9626b2ade65b713e58de02a3e90d9ce23536a344f061e6',
        'after': '7b1af5f9ca8f0b8a482026b06659331ae34ece98613a76b11cd7591a0e7d0103',
        'scope': 'A defaulted apex binder is selected on the symbolic registered schema before formal binder unification; existing DataPlan construction remains compatible'},
    'CasCatalogue/ComputationalData.lean': {
        'before': 'c0cb16055ad7fa6fc6086f0fd3863965a02164b8bfe6b1dba39eb5e68fe82c84',
        'after': '6eef76ad80969428447e6e0cae4cd421edff10c64652d36de8adf271bc9b20dc',
        'scope': 'Generic endpoint slots validate returned graph/named/opaque maps at distinct actual data roles; public lift-codec projection retains exact ownership; existing dispatchers remain separately compiled'},
    'CasCatalogue/ServiceRequest.lean': {
        'before': '4d1d2c5a4b11e63141b3eb10a8b1ed0650e55ab8263a42f40a5cf330017a8be3',
        'after': '94c82c2118483ce27541390bbb46558f33a91ac4e044f290d87963e05659c34f',
        'scope': 'Prepared retains exact endpoint operands and the independently selected typed method application; baseline uses its own original Prepared interface'},
    'CasCatalogue/SimpleServiceRequest.lean': {
        'before': '4937a53e5de24b73f335f80c6ee37a2c60a5ca649424b95d9dbf95b99625c219',
        'after': '9ac765d65312d1703e77420922d2b16c8c297da5db077f96243fbd05bb5feb22',
        'scope': 'Simple preparers retain exact typed operands and complete method descriptors without restarting execution through an Expr cache'},
    'CasCatalogue/StructuredServiceRequest.lean': {
        'before': '259d2fd6937020d8f7b5e76766bb4f651c7fcce1c74c0cb7238c103ed61e18f4',
        'after': '603924334dee68796c17c81ad061d890276597b3472de95cec39b2b840e77a71',
        'scope': 'Existing structured preparers retain exact typed callable endpoint operands'},
    'CasCatalogue/UniversalServiceRequest.lean': {
        'before': '4781b2991d976c080c47069461cac309f1dee946775a1b70a86f0548a60e04e5',
        'after': 'e3170277c6f31715e219455aa1ef315c1689db0bc72d6e165f6c5dad0b3e0d56',
        'scope': 'Universal invocations retain complete typed operands and actual lift action image data through the reviewed optional public metadata; legacy requests retain their recipe framing'},
    'CasCatalogue/ComputationDerivation.lean': {
        'before': '5db0786c3ce5766a6f1f2d298e4ad6135b3f3f3b08e666019ac81a4d054b84e5',
        'after': 'a8197d068b7094f013ff79ceae842a653d01a8e6046029a02d3398ae86898702',
        'scope': 'Retained typed method application and generic execution consumers; compiled independently of the historical kernel'},
    'CasCatalogue/LiftedSubobjectData.lean': {
        'before': '5e0cebc28b49eb3d437bc67a0d2a07e100655c2d0d360147d249ff6fd9d3afdf',
        'after': '4ef3bb20941f8d7956a33e950b25c6c82dd16f43a231e353a5b1882fe2c42ff6',
        'scope': 'Completed lift decoding keeps each actual source/comparison image and its ownership at independently selected formal interfaces; legacy packets preserve their explicit recipe mode'},
    'CasCatalogue/QuestionIdentity.lean': {
        'before': '31df18299a1074aca65ca5f0e61becc3867b7d16c1e00944bbe1c9ce17c32f32',
        'after': 'e3a241ebb78e40162dd60da280ab8e166fe53f2db1ac442734388b6c8cc01b02',
        'scope': 'Retained typed method application and generic execution consumers; compiled independently of the historical kernel'},
    'CasCatalogue/SelectedLift.lean': {
        'before': 'c055982c0bbf182399e8fe623e98190b4209fa912bebe0c81bbaf545069c3622',
        'after': '3b6398d73eb884c8052664e89048efd492c05c4d9aed2dd07c17ae2bc5eb8e1c',
        'scope': 'Retained typed method application and generic execution consumers; compiled independently of the historical kernel'},
    'CasCatalogue/Semantic.lean': {
        'before': 'd1ec8ea5007c039985b0fff5e0e6b4db4f53c1e68c03cdfef7663ee67e17f232',
        'after': 'abfa2269aa355d66ebebe3cb777cf1eac94bef34b967420d83f1da92ae280f50',
        'scope': 'Retained complete method and comparison applications, plus exact dependent limit choice validation; registry-only resolution and accepted creation/comparison constructions remain in use'},
    'CasCatalogue/Trace.lean': {
        'before': '5ffbe244154fcd65f5c889ffd45df302fa36d01436f6862bb48c14d78d0c20b7',
        'after': '544c4a440c3e99a426b90332ded7264cb9e9513544989a62796dc252fc36ff04',
        'scope': 'Retained typed method application and generic execution consumers; compiled independently of the historical kernel'},
}

# The reviewed contract adds a complete-method decoder and optional actual-image
# lift metadata. LiftInput/LiftFactorInput records, encoders and decoders change:
# defaults omit the new fields and preserve the legacy ordered wire arguments.
# Historical consumers construct/access named fields, not positional constructors.
# Both kernels use this effective contract tuple, recorded explicitly rather than
# misreported as the historical manifest; baseline sources are never rewritten.
REVIEWED_EXTERNAL_REVISIONS = {
    'cas_leaf_contracts': {
        'before': '3f7a22e0b6afc3e745f3aa60a9ceecf6740948d5',
        'after': '34bb8abbdbb49699015f63840cf86ed67f438003',
        'scope': 'Complete-method decoder, optional actual lift images, and accepted named-refinement comparison fields; changed Lean records/encoders/decoders and Python readers preserve legacy field order and absent-metadata behavior through defaults'},
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


def normalized_setup(path, source_root):
    """Keep compiler options/header semantics; resolve only artifact locations."""
    value = json.loads(path.read_text())
    if value.get('name') != MODULE or value.get('isModule') is not True \
            or value.get('imports') is not None or not isinstance(value.get('importArts'), dict) \
            or not value['importArts'] or MODULE in value['importArts']:
        raise ValueError('Expected a complete independently built Realize setup: ' + str(path))
    value['importArts'] = {
        module: [[str((source_root / item).resolve()) for item in group] for group in groups]
        for module, groups in value['importArts'].items()}
    value['dynlibs'] = [str((source_root / item).resolve()) for item in value.get('dynlibs', [])]
    value['plugins'] = [{**item, 'path': str((source_root / item['path']).resolve())}
                        for item in value.get('plugins', [])]
    return value


def reviewed_external_selection(root):
    """No changed mathematics, toolchain, package URL or unreviewed revision."""
    if git_bytes(root, 'show', BASELINE + ':lean-toolchain') != (root / 'lean-toolchain').read_bytes():
        raise ValueError('Baseline and candidate select different Lean toolchains')
    before = json.loads(git_bytes(root, 'show', BASELINE + ':lake-manifest.json'))
    after = json.loads((root / 'lake-manifest.json').read_text())
    original = {row['name']: row for row in before.pop('packages')}
    current = {row['name']: row for row in after.pop('packages')}
    if before != after or original.keys() != current.keys():
        raise ValueError('Baseline and candidate changed the external package configuration')
    changes = []
    for name, prior in original.items():
        selected = current[name]
        if prior == selected:
            continue
        reviewed = REVIEWED_EXTERNAL_REVISIONS.get(name)
        if reviewed is None or prior.get('rev') != reviewed['before'] \
                or selected.get('rev') != reviewed['after'] \
                or {**prior, 'rev': selected['rev']} != selected:
            raise ValueError('Unreviewed baseline external dependency change: ' + name)
        changes.append({'package': name, **reviewed, 'baselineDeclared': prior, 'effective': selected})
    return changes


def stage_baseline(root, baseline_root, directory, packages, guards):
    """Extract the fixed git archive; never rewrite a historical source/config."""
    if baseline_root.exists():
        raise ValueError('Refuse to replace an earlier isolated baseline checkout')
    archive = directory / 'baseline-source.tar'
    archive.write_bytes(git_bytes(root, 'archive', '--format=tar', BASELINE))
    baseline_root.mkdir()
    sources = []
    expected = {}
    for row in git_bytes(root, 'ls-tree', '-r', '-z', BASELINE).split(b'\0'):
        if not row:
            continue
        metadata, name = row.split(b'\t', 1)
        mode, kind, digest = metadata.decode().split()
        if kind != 'blob' or mode not in {'100644', '100755'}:
            raise ValueError('Baseline tree contains a nonordinary source entry')
        expected[name.decode()] = (mode, digest)
    extracted = set()
    with tarfile.open(fileobj=io.BytesIO(archive.read_bytes()), mode='r:') as entries:
        seen = set()
        for member in entries:
            relative = Path(member.name)
            if relative.is_absolute() or '..' in relative.parts or member.name in seen:
                raise ValueError('Unsafe or repeated path in fixed baseline archive')
            seen.add(member.name)
            target = baseline_root / relative
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            if not member.isfile():
                raise ValueError('Baseline archive requires ordinary source files: ' + member.name)
            data = entries.extractfile(member).read()
            digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            selected = expected.get(member.name)
            if selected is None or selected[1] != digest or bool(int(selected[0], 8) & 0o111) != bool(member.mode & 0o111):
                raise ValueError('Archived source differs from its exact baseline git blob: ' + member.name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            # git archive applies tar.umask to group-write bits; Git records
            # only ordinary/executable source modes. Restore that exact mode.
            target.chmod(int(selected[0], 8) & 0o777)
            extracted.add(member.name)
            sources.append(candidate.record(target))
    if extracted != expected.keys():
        raise ValueError('Baseline archive omitted a tracked source from the published tree')
    require_hash((baseline_root / REALIZE).read_bytes(), BASELINE_REALIZE_SHA256,
                 'Archived f65 Realize source')
    wrapper = directory / 'baseline-lake.sh'
    wrapper.write_text('#!/usr/bin/env bash\nset -euo pipefail\ncd -- ' +
                       shlex.quote(str(baseline_root)) + '\nexec lake --packages=' +
                       shlex.quote(str(packages)) + ' "$@"\n')
    guards.extend([candidate.record(archive), candidate.record(wrapper), *sources])
    return {'commit': BASELINE, 'tree': candidate.git(root, 'rev-parse', BASELINE + '^{tree}'),
            'archive': candidate.record(archive), 'root': str(baseline_root),
            'sources': sources, 'wrapper': candidate.record(wrapper)}


def baseline_dependencies(setup, baseline_root, candidate_root):
    """Every kernel import must come from the independently built old closure."""
    artifacts, sources = set(), []
    build_root = (baseline_root / '.lake/build').resolve()
    for module, groups in setup['importArts'].items():
        relative = Path(module.replace('.', '/') + '.lean')
        source = baseline_root / relative
        internal = source.is_file() or (candidate_root / relative).is_file()
        if internal and not source.is_file():
            raise ValueError('A baseline import names a candidate-only kernel module: ' + module)
        if internal:
            sources.append(candidate.record(source))
        for group in groups:
            for item in group:
                artifact = Path(item).resolve()
                if internal and not artifact.is_relative_to(build_root):
                    raise ValueError('Baseline imports a foreign kernel artifact: ' + module)
                artifacts.add(artifact)
    for item in setup.get('dynlibs', []):
        artifacts.add(Path(item))
    for item in setup.get('plugins', []):
        artifacts.add(Path(item['path']))
    return [candidate.record(path) for path in sorted(artifacts)], sources


def execute_controls(lean, setup, directory, modules, probes, current_parts,
                     baseline_source, baseline_setup, baseline_command, candidate_root,
                     step, guards, report):
    """All candidate checks run; a bad independent baseline build proves nothing."""
    successful = True
    for control in probes:
        name = control['name'] + '-candidate'
        selected = probe_setup(directory, name, control, setup, current_parts, guards)
        passed = step(name, [*lean, '--setup=' + str(selected), str(control['copy'])],
                      control['copy'])
        successful = passed and successful
    if not step('operation-owner-baseline-compile', baseline_command,
                baseline_source, build=True):
        report['baselineProbeDisposition'] = 'Not run: isolated baseline closure compilation failed'
        return False
    baseline_olean = modules / 'CasCatalogue/Realize.olean'
    baseline_parts = import_artifacts(baseline_olean)
    baseline_root = baseline_source.parent.parent
    baseline_imports = normalized_setup(baseline_setup, baseline_root)
    dependencies, sources = baseline_dependencies(baseline_imports, baseline_root, candidate_root)
    produced = [candidate.record(path) for group in baseline_parts for path in group]
    private = Path(str(baseline_olean) + '.private')
    if private.is_file():
        produced.append(candidate.record(private))
    report['baselineArtifacts'] = produced
    report['baselineDependencySetup'] = candidate.record(baseline_setup)
    report['baselineDependencyArtifacts'] = dependencies
    report['baselineKernelDependencySources'] = sources
    guards.extend([candidate.record(baseline_setup), *produced, *dependencies, *sources])
    for control in probes:
        if control['baselineErrors'] is None:
            continue
        name = control['name'] + '-baseline'
        selected = probe_setup(directory, name, control, baseline_imports, baseline_parts, guards)
        passed = step(name, [*lean, '--setup=' + str(selected), str(control['copy'])],
                      control['copy'], control['baselineErrors'])
        successful = passed and successful
    return successful


def run(root, runtime, published):
    evidence = runtime / 'evidence'
    directory = evidence / 'operation-owner-control'
    baseline_root = runtime / 'operation-owner-control-baseline'
    modules = baseline_root / '.lake/build/lib/lean'
    if directory.exists() or baseline_root.exists():
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
    external_changes = reviewed_external_selection(root)
    baseline_bytes = git_bytes(root, 'show', BASELINE + ':' + REALIZE)
    require_hash(baseline_bytes, BASELINE_REALIZE_SHA256, 'Published f65 Realize source')
    require_hash((root / REALIZE).read_bytes(), CANDIDATE_REALIZE_SHA256, 'Candidate Realize source')
    reviewed_sources = {}
    for relative, pair in REVIEWED_DEPENDENCY_SOURCES.items():
        reviewed_sources[relative] = reviewed_source_pair(root, relative, pair)

    setup_path = root / '.lake/build/ir/CasCatalogue/Realize.setup.json'
    setup = normalized_setup(setup_path, root)
    reviewed_modules = {path.removesuffix('.lean').replace('/', '.') for path in reviewed_sources}
    if setup.get('name') != MODULE or setup.get('isModule') is not True \
            or setup.get('imports') is not None or not isinstance(setup.get('importArts'), dict) \
            or not setup['importArts'] or MODULE in setup['importArts'] \
            or not reviewed_modules.issubset(setup['importArts']):
        raise ValueError('Expected the original complete Realize dependency setup without a header override')
    guards += [candidate.record(setup_path), candidate.record(root / REALIZE)]
    # Candidate imports keep their exact reviewed source/artifact closure. The
    # baseline is built separately below; none of these kernel artifacts are
    # overlaid into it. External package selection is independently checked.
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
    admission_runtime = directory / 'admission-configurations'
    admission_runtime.mkdir()
    baseline_tree = stage_baseline(root, baseline_root, directory, runtime / 'packages.json', guards)
    baseline_source = baseline_root / REALIZE
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
    baseline_setup = baseline_root / '.lake/build/ir/CasCatalogue/Realize.setup.json'
    for control in probes:
        path = directory / 'probes/CasAcceptance/Kernel' / (control['module'] + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(Path(control['original']['path']).read_bytes())
        control['copy'] = path
        guards.append(candidate.record(path))
    guards += [candidate.record(path) for path in
               [baseline_source, current_source]]
    environment = ['env', 'PYTHONDONTWRITEBYTECODE=1',
                   'CAS_OWNERSHIP_PROTOCOL_DIR=' + str(root / 'CasAcceptance/Strata'),
                   'CAS_OWNER_ADMISSION_RUNTIME_DIR=' + str(admission_runtime),
                   'CAS_LEAF_CONTRACT_PATH=' + str(contract),
                   'PYTHONPATH=' + str(contract / 'python')]
    lean = [*environment, 'bash', str(runtime / 'lake.sh'), 'env', 'lean', '--json']
    baseline_command = [*environment, 'bash', baseline_tree['wrapper']['path'], 'build', MODULE]
    report = {
        'purpose': 'Frozen action execution engineering controls; no mathematical or architectural acceptance',
        **gate, 'verifiedBuilds': builds, 'priorPureExports': pure_exports,
        'baselineDescription': 'Exact f65 kernel import closure rebuilt independently; fixed external tuple with the explicitly reviewed additive contract revision',
        'baselineSourceTree': baseline_tree,
        'baselineEffectiveExternalTuple': {name: item for name, item in producer.items() if name != 'kernel'},
        'reviewedExternalSelectionChanges': external_changes,
        'baselineKernelSourceCommit': BASELINE,
        'baselineBlob': candidate.git(root, 'rev-parse', BASELINE + ':' + REALIZE),
        'baselineSource': candidate.record(baseline_source),
        'candidateSource': candidate.record(current_source), 'candidateArtifacts': own_artifacts,
        'candidateDependencySetup': candidate.record(setup_path),
        'candidateDependencyArtifacts': dependency_artifacts,
        'candidateKernelDependencySources': kernel_dependencies,
        'reviewedCandidateSourceDeltas': deltas,
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

    def step(name, command, source, expected_errors=(), build=False):
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
        if build and expected_errors:
            raise ValueError('A baseline build cannot be treated as an expected red control')
        messages = None if build else diagnostics(Path(receipt['log']['path']))
        valid = (type(receipt['exit']) is int and receipt['exit'] == 0) if build else \
            check_diagnostics(messages, receipt['exit'], source, expected_errors)
        report['steps'][name] = {
            'invocation': candidate.record(path), 'diagnostics': messages,
            'diagnosticFormat': 'Lake build log; zero exit and compiled closure required' if build else 'Lean JSON diagnostics',
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
                            baseline_source, baseline_setup, baseline_command, root, step, guards, report):
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
                'CasCatalogue/ObjectPresentation.lean', 'CasCatalogue/FunctorActionData.lean',
                'CasCatalogue/StructuredProjection.lean',
                'CasCatalogue/ComputationalData.lean', 'CasCatalogue/ServiceRequest.lean',
                'CasCatalogue/SimpleServiceRequest.lean', 'CasCatalogue/StructuredServiceRequest.lean',
                'CasCatalogue/UniversalServiceRequest.lean', 'CasCatalogue/StructuredResult.lean',
                'CasCatalogue/DeclaredApplication.lean', 'CasCatalogue/RoutedResultPlan.lean',
                'CasCatalogue/Language.lean', 'CasCatalogue/LiftStageExecution.lean',
                'CasCatalogue/ComputationDerivation.lean', 'CasCatalogue/LiftedSubobjectData.lean', 'CasCatalogue/QuestionIdentity.lean', 'CasCatalogue/SelectedLift.lean', 'CasCatalogue/Semantic.lean', 'CasCatalogue/Trace.lean'})
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

    class BaselineIsolationTests(unittest.TestCase):
        def setUp(self):
            self.temp = tempfile.TemporaryDirectory()
            self.addCleanup(self.temp.cleanup)
            self.root = Path(self.temp.name)

        def test_only_reviewed_additive_external_revision_is_permitted(self):
            import sys
            this = sys.modules[__name__]
            old = {'packages': [
                {'name': 'cas_leaf_contracts', 'rev': REVIEWED_EXTERNAL_REVISIONS['cas_leaf_contracts']['before'], 'url': 'contract'},
                {'name': 'lean_categories', 'rev': 'fixed-mathematics', 'url': 'mathematics'}], 'version': '1.2.0'}
            new = copy.deepcopy(old)
            new['packages'][0]['rev'] = REVIEWED_EXTERNAL_REVISIONS['cas_leaf_contracts']['after']
            (self.root / 'lean-toolchain').write_bytes(b'fixed-toolchain')
            def fixed(_root, _command, reference):
                return b'fixed-toolchain' if reference.endswith(':lean-toolchain') else json.dumps(old).encode()
            with patch.object(this, 'git_bytes', side_effect=fixed):
                candidate.write(self.root / 'lake-manifest.json', new)
                self.assertEqual(len(reviewed_external_selection(self.root)), 1)
                for field, value in [('rev', 'different-contract'), ('url', 'another-repository')]:
                    changed = copy.deepcopy(new)
                    changed['packages'][0][field] = value
                    candidate.write(self.root / 'lake-manifest.json', changed)
                    with self.assertRaisesRegex(ValueError, 'Unreviewed baseline external'):
                        reviewed_external_selection(self.root)
                changed = copy.deepcopy(new)
                changed['packages'][1]['rev'] = 'different-mathematics'
                candidate.write(self.root / 'lake-manifest.json', changed)
                with self.assertRaisesRegex(ValueError, 'Unreviewed baseline external'):
                    reviewed_external_selection(self.root)
                candidate.write(self.root / 'lake-manifest.json', old)
                self.assertEqual(reviewed_external_selection(self.root), [])
                (self.root / 'lean-toolchain').write_bytes(b'changed-toolchain')
                with self.assertRaisesRegex(ValueError, 'different Lean toolchains'):
                    reviewed_external_selection(self.root)

        def test_fixed_archive_is_complete_exact_and_source_guarded(self):
            root = Path(__file__).resolve().parents[1]
            directory = self.root / 'evidence'
            directory.mkdir()
            checkout = self.root / 'independent-baseline'
            guards = []
            staged = stage_baseline(root, checkout, directory, self.root / 'packages.json', guards)
            self.assertEqual(staged['commit'], BASELINE)
            self.assertEqual((checkout / REALIZE).read_bytes(), git_bytes(root, 'show', BASELINE + ':' + REALIZE))
            self.assertEqual((checkout / 'CasCatalogue/Trace.lean').read_bytes(),
                             git_bytes(root, 'show', BASELINE + ':CasCatalogue/Trace.lean'))
            self.assertGreater(len(staged['sources']), 1)
            self.assertFalse((checkout / '.lake').exists())
            self.assertEqual(candidate.changed_records(guards), [])
            (checkout / 'CasCatalogue/Trace.lean').write_bytes(b'a candidate ABI cannot replace this source')
            self.assertIn(str(checkout / 'CasCatalogue/Trace.lean'), candidate.changed_records(guards))
            with self.assertRaisesRegex(ValueError, 'replace an earlier'):
                stage_baseline(root, checkout, directory, self.root / 'packages.json', guards)

        def test_candidate_artifact_cannot_enter_old_kernel_closure(self):
            baseline = self.root / 'baseline'
            source = baseline / 'CasCatalogue/Trace.lean'
            source.parent.mkdir(parents=True)
            source.write_bytes(b'old independent source')
            foreign = self.root / 'candidate/Trace.olean'
            foreign.parent.mkdir()
            foreign.write_bytes(b'new incompatible artifact')
            setup = {'importArts': {'CasCatalogue.Trace': [[str(foreign)], []]}}
            with self.assertRaisesRegex(ValueError, 'foreign kernel artifact'):
                baseline_dependencies(setup, baseline, self.root / 'candidate')

    class InvocationTests(unittest.TestCase):
        def setUp(self):
            self.temp = tempfile.TemporaryDirectory()
            self.addCleanup(self.temp.cleanup)
            self.root = Path(self.temp.name)
            self.directory = self.root / 'evidence'
            self.directory.mkdir()
            self.baseline_root = self.root / 'baseline-source'
            self.modules = self.baseline_root / '.lake/build/lib/lean'
            self.setup = {'name': MODULE, 'isModule': True, 'importArts': {
                'CasCatalogue.ComputationalData': [['current-dependency.olean'], ['current-dependency.ir']],
                'Lean': [[str(self.root / 'shared-lean.olean')], []]}, 'options': {'retain': 'original'}}
            (self.root / 'shared-lean.olean').write_bytes(b'unchanged external Lean fixture')
            self.setup_original = copy.deepcopy(self.setup)
            self.baseline_source = self.baseline_root / REALIZE
            self.baseline_source.parent.mkdir(parents=True)
            self.baseline_dependency = self.baseline_root / 'CasCatalogue/ComputationalData.lean'
            self.baseline_dependency.write_bytes(b'unchanged old dependency fixture')
            self.baseline_source.write_bytes(b'unchanged original baseline source\n')
            self.baseline_setup = self.baseline_root / '.lake/build/ir/CasCatalogue/Realize.setup.json'
            self.baseline_command = ['lake', 'build', MODULE]
            self.current_parts = [['candidate.olean', 'candidate.olean.server'],
                                  ['candidate.ir.sig', 'candidate.ir']]
            self.probes = []
            for control in CONTROLS:
                source = self.root / (control['module'] + '.lean')
                source.write_text(control['module'] + ': immutable source fixture\n')
                self.probes.append({**control, 'copy': source})
            self.guards = [candidate.record(self.baseline_source), candidate.record(self.baseline_dependency)]
            self.guards += [candidate.record(control['copy']) for control in self.probes]
            self.report = {}

        def execute(self, failures=(), omit_artifacts=False):
            def invoke(name, command, source, expected_errors=(), build=False):
                if build:
                    self.assertEqual(command, self.baseline_command)
                    self.assertEqual(expected_errors, ())
                else:
                    self.assertEqual(command[-1], str(source))
                self.assertFalse(any('heartbeats' in value or 'maxRecDepth' in value for value in command))
                self.assertTrue(str(source).startswith(str(self.root)))
                if name == 'operation-owner-baseline-compile' and name not in failures and not omit_artifacts:
                    for module in ['CasCatalogue/ComputationalData', 'CasCatalogue/Realize']:
                        olean = self.modules / (module + '.olean')
                        olean.parent.mkdir(parents=True, exist_ok=True)
                        for path in [olean, Path(str(olean) + '.server'),
                                     olean.with_suffix('.ir.sig'), olean.with_suffix('.ir'),
                                     Path(str(olean) + '.private')]:
                            path.write_bytes(b'independent historical module fixture\n')
                    independent = copy.deepcopy(self.setup)
                    independent['importArts']['CasCatalogue.ComputationalData'] = import_artifacts(
                        self.modules / 'CasCatalogue/ComputationalData.olean')
                    candidate.write(self.baseline_setup, independent)
                return name not in failures
            self.step = Mock(side_effect=invoke)
            return execute_controls(['lean', '--json'], self.setup, self.directory, self.modules,
                                    self.probes, self.current_parts, self.baseline_source,
                                    self.baseline_setup, self.baseline_command, self.root,
                                    self.step, self.guards, self.report)

        def test_exact_matrix_with_isolated_kernel_artifacts(self):
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
                    self.assertEqual(source.read_bytes(), b'unchanged original baseline source\n')
                    self.assertTrue(call.kwargs.get('build'))
                    self.assertEqual(source, self.baseline_source)
                    self.assertFalse(expected)
                    continue
                selected = json.loads(Path(next(value.split('=', 1)[1] for value in command
                                                if value.startswith('--setup='))).read_text())
                parts = selected['importArts'].pop(MODULE)
                expected_imports = copy.deepcopy(self.setup_original['importArts'])
                if name.endswith('-baseline'):
                    expected_imports['CasCatalogue.ComputationalData'] = import_artifacts(
                        self.modules / 'CasCatalogue/ComputationalData.olean')
                self.assertEqual(selected['importArts'], expected_imports)
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
        unittest.defaultTestLoader.loadTestsFromTestCase(BaselineIsolationTests),
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
