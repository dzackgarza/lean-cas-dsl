#!/usr/bin/env python3
"""Run the existing connected examples and notebook on the built CI candidate.

This is invocation wiring for the existing production surface and its existing
17-result checker. It neither supplies mathematics nor accepts an MVP release.
The two original specimen revisions remain separate and unchanged. Outputs,
Python environments and the private kernelspec live outside all source trees.
"""

import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time

import ci_kernel_candidate as candidate


LEAVES = {
    'workflowLeaves': '2c8b9040ea68513c34817f5c7b6fa5a5ce6b1252',
    'existingLeaves': '865df49ad0b0b133d5bcfd282f380aa213eb5fff',
}
LEAF_REPOSITORY = 'https://github.com/dzackgarza/lean-cas-dsl-leaves.git'


def restore_leaves(runtime):
    sources = {}
    for name, revision in LEAVES.items():
        path = runtime / 'workflow-sources' / name
        if path.exists():
            raise ValueError('Refuse to replace a workflow source checkout: ' + str(path))
        log = runtime / 'evidence' / ('fetch-' + name + '.log')
        with log.open('x') as stream:
            for command in [
                    ['git', 'init', str(path)],
                    ['git', '-C', str(path), 'remote', 'add', 'origin', LEAF_REPOSITORY],
                    ['git', '-C', str(path), 'fetch', '--depth', '1', 'origin', revision],
                    ['git', '-C', str(path), 'checkout', '--detach', 'FETCH_HEAD']]:
                subprocess.run(command, check=True, stdout=stream, stderr=subprocess.STDOUT)
        source = candidate.state(path)
        if source['commit'] != revision or source['workingTree']:
            raise ValueError('Workflow specimen differs from its exact clean revision')
        sources[name] = source
    return sources


def execution_artifacts(root, selected):
    """Hash the production notebook's owned import closure and native tools."""
    setup = root / '.lake/build/ir/CasDsl/Notebook.setup.json'
    modules = set(json.loads(setup.read_text()).get('importArts', {})) | {'CasDsl.Notebook'}
    worker = next(path for name, path in selected.items() if name.strip('«»') == 'nbdsl-worker')
    paths = {root / '.lake/build/bin/cas-harness',
             worker / '.lake/build/bin/nbdsl_worker', setup}
    for module in modules:
        if not module.startswith(('CasCatalogue', 'CasDsl', 'CasTools',
                                  'CasContract', 'LeanCategories', 'Worker')):
            continue
        relative = Path(*module.split('.'))
        package = next((path for path in [root, *selected.values()]
                        if (path / '.lake/build/lib/lean' / relative.with_suffix('.olean')).is_file()), None)
        if package is None:
            raise ValueError('Missing built production import: ' + module)
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig']:
            path = package / '.lake/build/lib/lean' / Path(str(relative) + suffix)
            if path.is_file():
                paths.add(path)
    return {str(path): candidate.record(path) for path in sorted(paths)}


def run(root, runtime, published):
    evidence = runtime / 'evidence'
    report_path = evidence / 'connected-workflows-summary.json'
    if report_path.exists():
        raise ValueError('Refuse to replace earlier connected workflow evidence')
    gate = candidate.export_gate(root, runtime, published)
    producer = gate['producer']
    for name in ['consumers', 'native', 'axiom-audit']:
        receipt = json.loads((evidence / (name + '-provenance.json')).read_text())
        if (receipt.get('status') != 'completed' or receipt.get('exit') != 0
                or receipt.get('sourceTupleChanged') is not False
                or receipt.get('producer') != producer
                or receipt.get('producerAfter') != producer
                or candidate.record(receipt['log']['path']) != receipt['log']):
            raise ValueError('A matching completed source-stable ' + name + ' run is required')
    selected = {row['name']: Path(row['dir'])
                for row in json.loads((runtime / 'packages.json').read_text())['packages']}
    worker_root = next(path for name, path in selected.items() if name.strip('«»') == 'nbdsl-worker')
    notebook_package = worker_root.parent / 'nbdsl_kernel'
    if not (notebook_package / 'pyproject.toml').is_file():
        raise ValueError('Selected notebook dependency has no existing Python adapter')
    sage = os.environ.get('CAS_SAGE_PYTHON')
    lake = shutil.which('lake')
    if not sage or not Path(sage).is_file() or not lake:
        raise ValueError('Use the installed candidate engines and Lean toolchain')
    os.environ['PYTHONDONTWRITEBYTECODE'] = '1'
    leaf_sources = restore_leaves(runtime)
    sources = {**producer, **leaf_sources}
    diagnostic = Path(leaf_sources['workflowLeaves']['path']) / 'diagnostics/v1/leaves.json'
    existing = Path(leaf_sources['existingLeaves']['path']) / 'leaves.json'
    notebook = root / 'notebooks/kernel-v1.ipynb'
    fixed_paths = [notebook, diagnostic, existing, runtime / 'packages.json',
                   root / 'scripts/run_kernel_v1_demo.py',
                   root / 'scripts/execute_kernel_notebook.py', Path(__file__),
                   root / 'examples/kernel-v1/requirements-notebook-py312.txt',
                   *sorted((root / 'examples/kernel-v1').glob('*.cas'))]
    fixed = {item['path']: item for item in gate['guardedInputs']}
    fixed.update({str(path): candidate.record(path) for path in fixed_paths})
    generated_inputs = {}
    artifacts = execution_artifacts(root, selected)
    report = {
        'purpose': 'Existing connected workflows and notebook; no mathematical admission or MVP acceptance',
        'producer': sources, 'publishedKernel': published,
        'verifiedBuild': gate['verifiedBuild'], 'readerPreflight': gate['readerPreflight'],
        'startedUtc': candidate.stamp(), 'status': 'running', 'steps': [],
        'fixedInputs': fixed, 'artifactsBefore': artifacts,
        'sourceSelection': 'Original diagnostic specimen plus only the two existing Sets registrations',
    }
    candidate.write(report_path, report)
    start = time.monotonic()
    code = 1

    def step(name, command):
        try:
            candidate.run(root, runtime, name, command)
        finally:
            receipt = evidence / (name + '-provenance.json')
            if receipt.is_file():
                report['steps'].append(candidate.record(receipt))
                candidate.write(report_path, report)
        return evidence / (name + '.log')

    def demo_arguments(output):
        return [str(root / 'scripts/run_kernel_v1_demo.py'),
                '--contract', str(selected['cas_leaf_contracts']),
                '--sage-python', sage, '--diagnostic-manifest', str(diagnostic),
                '--leaves-manifest', str(existing), '--packages', str(runtime / 'packages.json'),
                '--lake', lake, '--output', str(output)]

    try:
        cli_output = evidence / 'connected-workflows'
        if cli_output.exists():
            raise ValueError('Connected CLI output already exists')
        step('connected-cli', [sys.executable, *demo_arguments(cli_output)])
        report['cliReport'] = candidate.record(cli_output / 'report.json')

        notebook_runtime = runtime / 'notebook-runtime'
        notebook_runtime.mkdir()
        python = notebook_runtime / 'venv/bin/python'
        step('notebook-python', ['uv', 'venv', '--python', sage, str(python.parent.parent)])
        step('notebook-dependencies', [
            'uv', 'pip', 'install', '--default-index', 'https://pypi.org/simple',
            '--only-binary=:all:', '--strict', '--python', str(python),
            '--requirements', str(root / 'examples/kernel-v1/requirements-notebook-py312.txt')])
        step('notebook-adapter', [
            'uv', 'pip', 'install', '--default-index', 'https://pypi.org/simple',
            '--no-deps', '--python', str(python), str(notebook_package)])
        step('notebook-environment', [str(python), '-c',
            'import importlib.metadata,json,platform; '
            'print(json.dumps({"python":platform.python_version(),'
            '"packages":{d.metadata["Name"]:d.version '
            'for d in importlib.metadata.distributions()}},indent=2))'])

        # The existing adapter asks `lake env` and locates the already-built
        # worker. Bind those two invocations to the exact selected dependencies;
        # do not rewrite a source manifest or ask the notebook to build anything.
        bin_dir = notebook_runtime / 'bin'
        bin_dir.mkdir()
        wrapper = bin_dir / 'lake'
        wrapper.write_text('#!/usr/bin/env bash\nset -euo pipefail\nexec ' +
                           shlex.quote(lake) + ' --packages=' +
                           shlex.quote(str(runtime / 'packages.json')) + ' "$@"\n')
        wrapper.chmod(0o755)
        selected_worker = worker_root / '.lake/build/bin/nbdsl_worker'
        link = root / '.lake/build/bin/nbdsl_worker'
        if link.exists() or link.is_symlink():
            if link.resolve() != selected_worker.resolve():
                raise ValueError('An existing worker binding selects a different executable')
        else:
            link.symlink_to(selected_worker.resolve())
        report['workerBinding'] = {'path': str(link), 'target': str(link.resolve())}
        report['lakeBinding'] = candidate.record(wrapper)
        generated_inputs[str(wrapper)] = report['lakeBinding']

        output = evidence / 'notebook'
        output.mkdir()
        prepared = output / 'demo'
        preparation = step('notebook-prepare', [str(python), *demo_arguments(prepared), '--prepare-only'])
        commands = [line for line in preparation.read_text().splitlines()
                    if line.startswith('#cas_tests ')]
        if len(commands) != 1:
            raise ValueError('The existing demo preparer omitted its unique notebook command')
        original = json.loads(notebook.read_text())
        cells = [cell for cell in original['cells'] if cell['cell_type'] == 'code']
        if len(original['cells']) != 6 or len(cells) != 1:
            raise ValueError('The existing notebook no longer has its original six-cell surface')
        cells[0].update(source=commands[0] + '\n', outputs=[], execution_count=None)
        adapted = output / 'kernel-v1-path-adapted.ipynb'
        candidate.write(adapted, original)
        report['notebookAdaptation'] = {
            'source': fixed[str(notebook)], 'copy': candidate.record(adapted),
            'change': 'Only runtime paths in the existing code cell; same production command and examples',
            'command': commands[0]}
        generated_inputs[str(adapted)] = candidate.record(adapted)
        environment = {
            'PATH': str(bin_dir) + os.pathsep + str(python.parent) + os.pathsep + os.environ.get('PATH', ''),
            'CAS_LEAF_CONTRACT_PATH': str(selected['cas_leaf_contracts']),
            'CAS_LEAVES': str(prepared / 'leaves.json'),
            'JUPYTER_DATA_DIR': str(notebook_runtime / 'jupyter-data'),
            'JUPYTER_RUNTIME_DIR': str(notebook_runtime / 'jupyter-runtime'),
            'JUPYTER_CONFIG_DIR': str(notebook_runtime / 'jupyter-config'),
            'IPYTHONDIR': str(notebook_runtime / 'ipython'),
        }
        prefix = ['env', *[key + '=' + value for key, value in environment.items()]]
        report['notebookEnvironment'] = environment
        step('notebook-kernelspec', [*prefix, str(python), '-m', 'nbdsl_kernel.install',
            '--project', str(root), '--name', 'casdsl', '--display-name', 'CasDsl (Lean 4)',
            '--prelude-module', 'CasDsl.Notebook'])
        spec = notebook_runtime / 'jupyter-data/kernels/casdsl/kernel.json'
        report['kernelSpec'] = candidate.record(spec)
        generated_inputs[str(spec)] = report['kernelSpec']
        shutil.copyfile(spec, output / 'kernel.json')
        executed = output / 'kernel-v1-executed.ipynb'
        step('notebook-execution', [*prefix, str(python), str(root / 'scripts/execute_kernel_notebook.py'),
            '--input', str(adapted), '--output', str(executed), '--cwd', str(root)])
        step('notebook-report-check', [str(python), str(root / 'scripts/run_kernel_v1_demo.py'),
            '--check-report', str(prepared / 'notebook-report.json')])
        report['executedNotebook'] = candidate.record(executed)
        report['notebookReport'] = candidate.record(prepared / 'notebook-report.json')
        code = 0
    except (Exception, SystemExit) as error:
        report['error'] = repr(error)
    finally:
        after = {name: candidate.state(Path(row['path'])) for name, row in sources.items()}
        report.update(status='completed', finishedUtc=candidate.stamp(),
                      seconds=round(time.monotonic() - start, 3), producerAfter=after,
                      sourceTupleChanged=sources != after)
        report['fixedInputChanges'] = [path for path, item in fixed.items()
                                      if not Path(path).is_file() or candidate.record(path) != item]
        report['generatedInvocationInputs'] = generated_inputs
        report['generatedInputChanges'] = [path for path, item in generated_inputs.items()
                                          if not Path(path).is_file() or candidate.record(path) != item]
        report['artifactChanges'] = [path for path, item in artifacts.items()
                                    if not Path(path).is_file() or candidate.record(path) != item]
        if (report['sourceTupleChanged'] or report['fixedInputChanges']
                or report['generatedInputChanges'] or report['artifactChanges']):
            code = 2
        report['exit'] = code
        report['completeConnectedExecution'] = code == 0
        candidate.write(report_path, report)
    print(json.dumps({'report': str(report_path), 'exit': code,
                      'error': report.get('error')}), flush=True)
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--runtime', type=Path,
                        default=Path(os.environ.get('RUNNER_TEMP', '/tmp')) / 'kernel-v1-candidate')
    parser.add_argument('--published-kernel-commit', default=os.environ.get('GITHUB_SHA'),
                        help='explicit published source SHA; defaults to the Actions checkout SHA')
    args = parser.parse_args()
    if not args.published_kernel_commit:
        parser.error('provide --published-kernel-commit outside GitHub Actions')
    return run(args.root.resolve(), args.runtime.resolve(), args.published_kernel_commit)


if __name__ == '__main__':
    raise SystemExit(main())
