#!/usr/bin/env python3
"""Prepare or publish the verified accepted-input configuration through its protected PR.

Default mode prints the exact reviewable operation and writes nothing remotely.
--publish is a trusted operator operation, never an exposed author capability.
It uses existing GitHub authentication and never bypasses accepted-ref protections.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from apply_assessment import assemble


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('configuration','request','decision','signature'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--deployment-repository',type=Path,required=True)
    parser.add_argument('--github-repository',default='dzackgarza/lean-cas-dsl')
    parser.add_argument('--publish',action='store_true')
    args=parser.parse_args()
    next_config=assemble(args.configuration,args.request,args.decision,args.signature)
    request=json.loads(args.request.read_text())
    request_id=request['request_id']
    head='custodian/assessment-'+request_id[:20]
    plan={'repository':args.github_repository,'base':'accepted/controller','head':head,
          'path':'custodian/deployment.json','evidence_path':'custodian/admission/'+request_id,'request_id':request_id,
          'next_configuration_sha256':hashlib.sha256(json.dumps(next_config,sort_keys=True,separators=(',',':')).encode()).hexdigest()}
    if not args.publish:
        print(json.dumps(plan,sort_keys=True));return 0
    # Source publication is performed in a fresh disposable clone, preserving owner work.
    # No candidate Python or workflow code is executed while credentials are present.
    with tempfile.TemporaryDirectory(prefix='custodian-publication-') as tmp:
        checkout=Path(tmp)/'deployment'
        def command(*cmd):return subprocess.run(cmd,check=True,capture_output=True,text=True).stdout.strip()
        command('git','-c','core.hooksPath=/dev/null','clone','--quiet','--no-hardlinks','--',str(args.deployment_repository),str(checkout))
        command('git','-C',str(checkout),'remote','set-url','origin','https://github.com/'+args.github_repository+'.git')
        command('git','-c','core.hooksPath=/dev/null','-C',str(checkout),'fetch','--quiet','origin','accepted/controller')
        command('git','-c','core.hooksPath=/dev/null','-C',str(checkout),'checkout','--quiet','-b',head,'FETCH_HEAD')
        baseline=json.loads((checkout/'custodian/deployment.json').read_text())
        supplied=json.loads(args.configuration.read_text())
        if baseline!=supplied:raise ValueError('protected deployment advanced; reassemble against its current input tuple')
        (checkout/'custodian/deployment.json').write_text(json.dumps(next_config,indent=2,sort_keys=True)+'\n')
        evidence=checkout/'custodian/admission'/request_id
        evidence.mkdir(parents=True,exist_ok=False)
        for name,source in [('request.json',args.request),('decision.json',args.decision),('decision.json.sig',args.signature)]:
            (evidence/name).write_bytes(source.read_bytes())
        command('git','-c','core.hooksPath=/dev/null','-C',str(checkout),'add','--','custodian/deployment.json','custodian/admission/'+request_id)
        command('git','-c','core.hooksPath=/dev/null','-C',str(checkout),'-c','user.name=custodian-publication','-c','user.email=custodian-publication@users.noreply.github.com','commit','--quiet','-m','Advance independently assessed immutable input tuple')
        command('git','-c','core.hooksPath=/dev/null','-C',str(checkout),'push','--quiet','origin','HEAD:refs/heads/'+head)
        body=Path(tmp)/'body.md'
        body.write_text('Advance the immutable input tuple assessed by independently signed request `'+request_id+'`.\n\nThe configuration was reconstructed from those exact revisions and verified against the configured independent review identity. This is input advancement; it does not declare B0 complete.\n')
        url=command('gh','pr','create','--repo',args.github_repository,'--base','accepted/controller','--head',head,'--title','Advance independently assessed inputs','--body-file',str(body))
        print(url)
    return 0

if __name__=='__main__':raise SystemExit(main())
