#!/usr/bin/env python3
"""Prepare isolated engineering fixtures with test-only SSH keys; no acceptance grant."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--scratch',type=Path,required=True)
    args=parser.parse_args()
    if args.scratch.exists():raise ValueError('use an absent scratch directory')
    args.scratch.mkdir(parents=True)
    source=args.scratch/'source';source.mkdir()
    def run(*args):return subprocess.run(args,check=True,capture_output=True,text=True).stdout.strip()
    archive=subprocess.run(['git','-C',str(args.source),'archive','HEAD'],check=True,capture_output=True).stdout
    import io,tarfile
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:tar.extractall(source,filter='data')
    shutil.copytree(args.source/'custodian',source/'custodian',dirs_exist_ok=True)
    shutil.rmtree(source/'custodian/verdicts',ignore_errors=True)
    (source/'custodian/verdicts').mkdir()
    def init(repo):
        run('git','init','-q',str(repo));run('git','-C',str(repo),'config','user.name','fixture');run('git','-C',str(repo),'config','user.email','fixture@example.test')
    def commit(repo):run('git','-C',str(repo),'add','-A');run('git','-C',str(repo),'commit','-qm','engineering fixture')
    init(source)
    manifest={'version':'1.1.0','packages':[]}
    for name,path in (('lean_categories','LeanCategories/Catalogue.lean'),('cas_leaf_contracts','CasContract.lean'),('cas_leaves','CasLeaves.lean')):
        repo=source/'.lake/packages'/name;repo.mkdir(parents=True);init(repo)
        target=repo/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('-- engineering fixture\n');commit(repo)
        manifest['packages'].append({'name':name,'rev':run('git','-C',str(repo),'rev-parse','HEAD')})
    (source/'lake-manifest.json').write_text(json.dumps(manifest))
    for name in ('root','review','escalation'):
        run('ssh-keygen','-q','-t','ed25519','-N','','-f',str(args.scratch/name))
    shutil.copy(args.scratch/'root.pub',source/'custodian/root.pub');commit(source)
    run('python3',str(source/'custodian/verify.py'),'--repo',str(source),'--seal',str(source/'custodian/seal.json'),'--make-seal','--reviewer-key',str(args.scratch/'review.pub'),'--escalation-key',str(args.scratch/'escalation.pub'))
    (source/'custodian/seal.json.sig').unlink(missing_ok=True)
    run('ssh-keygen','-q','-Y','sign','-f',str(args.scratch/'root'),'-n','lean-cas-custodian',str(source/'custodian/seal.json'));commit(source)
    fingerprint=run('ssh-keygen','-lf',str(args.scratch/'root.pub')).split()[1]
    output=args.scratch/'tests';output.mkdir()
    result=subprocess.run(['python3',str(args.source/'custodian/review/test_review.py'),str(output),str(source),str(args.scratch/'review'),str(args.scratch/'escalation'),fingerprint])
    return result.returncode

if __name__=='__main__':raise SystemExit(main())
