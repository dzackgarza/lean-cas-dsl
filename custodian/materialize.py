#!/usr/bin/env python3
"""Read-only retrieval of launcher-configured immutable inputs. Never executes candidates."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configuration',type=Path,required=True)
    parser.add_argument('--candidate',required=True)
    args=parser.parse_args()
    if not re.fullmatch(r'[0-9a-f]{40}',args.candidate):parser.error('full candidate commit required')
    config=json.loads(args.configuration.read_text())
    entries=[config['requirements'],*[v for v in config['accepted'].values() if 'artifact_file' not in v]]
    for value in config['accepted'].values():
        if 'artifact_file' not in value:continue
        path=Path(value['artifact_file'])
        if not path.is_file():raise ValueError('protected external release artifact must be provisioned before assessment')
        if hashlib.sha256(path.read_bytes()).hexdigest()!=value['sha256']:raise ValueError('protected external release artifact digest mismatch')
    by_path={}
    for entry in entries:
        path=Path(entry['repository'])
        if path in by_path and by_path[path]!=entry['url']:
            raise ValueError('repository tuple identity disagreement')
        by_path[path]=entry['url']
    for path,url in by_path.items():
        if path.exists():raise ValueError('materialization destination already exists')
        path.parent.mkdir(parents=True,exist_ok=True)
        subprocess.run(['git','-c','core.hooksPath=/dev/null','clone','--quiet','--no-checkout','--',url,str(path)],check=True)
    history=config.get('rejections')
    if history:
        subprocess.run(['git','-c','core.hooksPath=/dev/null','clone','--quiet','--branch',history['ref'],'--',history['url'],history['repository']],check=True)
    for entry in entries:
        if not re.fullmatch(r'[0-9a-f]{40}',entry['commit']):raise ValueError('full configured revision required')
        subprocess.run(['git','-C',entry['repository'],'cat-file','-e',entry['commit']+'^{commit}'],check=True)
    component=config['review_component']
    source=config['accepted'][component]['repository']
    subprocess.run(['git','-c','core.hooksPath=/dev/null','-C',source,'fetch','--quiet','origin','--',args.candidate],check=True)
    return 0

if __name__=='__main__':raise SystemExit(main())
