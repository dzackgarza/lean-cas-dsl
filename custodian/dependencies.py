"""Resolve source dependencies at invocation; never advance protected judging inputs.

The resulting commit identities are reproducibility snapshots. Applying an already
signed assessment deliberately uses its captured configuration without resolving again.
"""
import copy
from pathlib import Path
from controller import git


SOURCE_DEPENDENCIES = frozenset(('mathematics', 'contract', 'leaves', 'notebook'))


def resolve_dependencies(configuration):
    config = copy.deepcopy(configuration)
    for name, entry in config['accepted'].items():
        if name not in SOURCE_DEPENDENCIES:
            continue
        if 'artifact_file' in entry or 'path' in entry:
            raise ValueError('source dependency cannot be a fixed artifact')
        repository = Path(entry['repository'])
        remote = entry.get('url', 'origin')
        git(repository, 'fetch', '--quiet', '--no-tags', '--', remote, 'refs/heads/main')
        entry['commit'] = git(repository, 'rev-parse', 'FETCH_HEAD^{commit}').decode().strip()
    source = config.get('source_base')
    if source is not None:
        for name in SOURCE_DEPENDENCIES.intersection(config['accepted']):
            entry = config['accepted'][name]
            if Path(source['repository']).resolve() == Path(entry['repository']).resolve():
                source['commit'] = entry['commit']
    public = config['accepted'].get('public_metadata')
    if public is not None:
        provenance = public.get('provenance')
        if provenance is not None:
            for name in ('mathematics', 'contract'):
                if name not in config['accepted'] or provenance.get(name) != config['accepted'][name]['commit']:
                    raise ValueError('fixed public metadata provenance differs from current main')
        elif 'mathematics' in config['accepted'] and public['commit'] != config['accepted']['mathematics']['commit']:
            raise ValueError('fixed public metadata source differs from current main')
    return config
