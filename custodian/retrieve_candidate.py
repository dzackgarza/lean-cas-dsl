#!/usr/bin/env python3
"""Retrieve candidate Git data without checkout, hooks, filters or candidate execution."""
import argparse
import os
from pathlib import Path
import re
import subprocess


def retrieve(repository, reference, expected, destination):
    if not re.fullmatch('[0-9a-f]{40}', expected):
        raise ValueError('full candidate SHA required')
    destination.mkdir()
    environment = {'PATH': os.defpath, 'LANG': 'C.UTF-8',
                   'GIT_CONFIG_GLOBAL': '/dev/null', 'GIT_CONFIG_NOSYSTEM': '1'}
    def git(*args):
        return subprocess.run(['git', '-c', 'core.hooksPath=/dev/null', '-C', str(destination), *args],
                              env=environment, check=True, capture_output=True).stdout
    git('init', '--quiet')
    git('fetch', '--quiet', '--no-tags', '--', repository, reference)
    actual = git('rev-parse', 'FETCH_HEAD^{commit}').decode().strip()
    if actual != expected:
        raise ValueError('candidate reference moved from event SHA')
    entries = []
    for record in git('ls-tree', '-rz', '--full-tree', expected).split(b'\0'):
        if not record:
            continue
        metadata, raw_path = record.split(b'\t', 1)
        mode, kind, object_id = metadata.split()
        path = Path(os.fsdecode(raw_path))
        if mode not in (b'100644', b'100755') or kind != b'blob':
            raise ValueError('candidate contains a link or nonregular file')
        if path.is_absolute() or '..' in path.parts or any(p.lower() == '.git' for p in path.parts) or '\\' in str(path):
            raise ValueError('candidate path escapes regular source tree')
        entries.append((path, mode, object_id.decode()))
    # Validate the complete tree before exposing any candidate paths.
    for path, mode, object_id in entries:
        target = destination/path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(git('cat-file', 'blob', object_id))
        target.chmod(0o755 if mode == b'100755' else 0o644)
    git('read-tree', expected)
    git('update-ref', 'HEAD', expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--reference', required=True)
    parser.add_argument('--expected', required=True)
    parser.add_argument('--destination', type=Path, required=True)
    args = parser.parse_args()
    retrieve(args.repository, args.reference, args.expected, args.destination)


if __name__ == '__main__':
    main()
