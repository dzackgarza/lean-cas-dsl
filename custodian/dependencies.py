"""Resolve source dependencies at invocation; never advance protected judging inputs.

The resulting commit identities are reproducibility snapshots. Applying an already
signed assessment deliberately uses its captured configuration without resolving again.
"""
import copy
from pathlib import Path
from controller import git


SOURCE_DEPENDENCIES = frozenset(('mathematics', 'contract', 'leaves', 'notebook'))


def resolve_dependencies(configuration, inputs=None):
    config = copy.deepcopy(configuration)
    consumed = set(config['accepted']) if inputs is None else set(inputs)
    if 'public_metadata' in consumed:
        consumed.update(('mathematics', 'contract'))
    for name, entry in config['accepted'].items():
        if name not in SOURCE_DEPENDENCIES.intersection(consumed):
            continue
        if 'artifact_file' in entry or 'path' in entry:
            raise ValueError('source dependency cannot be a fixed artifact')
        repository = Path(entry['repository'])
        remote = entry.get('url', 'origin')
        git(repository, 'fetch', '--quiet', '--no-tags', '--', remote, 'refs/heads/main')
        entry['commit'] = git(repository, 'rev-parse', 'FETCH_HEAD^{commit}').decode().strip()
    source = config.get('source_base')
    if source is not None:
        for name in SOURCE_DEPENDENCIES.intersection(config['accepted'], consumed):
            entry = config['accepted'][name]
            if Path(source['repository']).resolve() == Path(entry['repository']).resolve():
                source['commit'] = entry['commit']
    public = config['accepted'].get('public_metadata')
    if 'public_metadata' in consumed and public is not None:
        if not ('path' in public or 'artifact_file' in public):
            raise ValueError('public metadata requires a fixed artifact descriptor')
        provenance = public.get('provenance')
        if not isinstance(provenance, dict):
            raise ValueError('public metadata requires mathematics and contract provenance')
        for name in ('mathematics', 'contract'):
            if name not in config['accepted'] or provenance.get(name) != config['accepted'][name]['commit']:
                raise ValueError('fixed public metadata provenance differs from current main')
    return config
