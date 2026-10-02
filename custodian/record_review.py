#!/usr/bin/env python3
"""Append a verified judgment to the existing signed review discussion branch."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
from controller import canonical, verify_review_signature


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('configuration','out'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    cfg=json.loads(args.configuration.read_text())
    decision=args.out/'decision.json';signature=Path(str(decision)+'.sig')
    if not decision.exists():return 0 # invocation failure produced no judgment
    verify_review_signature(decision,signature,Path(cfg['reviewer_public_key']),cfg['reviewer_fingerprint'])
    request=json.loads((args.out/'request.json').read_text())
    request_id=request.pop('request_id')
    if hashlib.sha256(canonical(request)).hexdigest()!=request_id:raise ValueError('invalid snapshot digest')
    value=json.loads(decision.read_text())
    if value['request_id']!=request_id:raise ValueError('judgment belongs to another discussion')
    history=Path(cfg['rejections']['repository'])
    (history/(request_id+'.json')).write_bytes(decision.read_bytes())
    (history/(request_id+'.json.sig')).write_bytes(signature.read_bytes())
    subprocess.run(['git','-c','core.hooksPath=/dev/null','-C',str(history),'add','--',request_id+'.json',request_id+'.json.sig'],check=True)
    clean=subprocess.run(['git','-C',str(history),'diff','--cached','--quiet']).returncode==0
    if clean:return 0
    subprocess.run(['git','-c','core.hooksPath=/dev/null','-C',str(history),'-c','user.name=custodian-review','-c','user.email=custodian-review@users.noreply.github.com','commit','--quiet','-m','Record independently signed review discussion '+request_id[:16]],check=True)
    subprocess.run(['git','-c','core.hooksPath=/dev/null','-C',str(history),'push','--quiet','origin','HEAD:'+cfg['rejections']['ref']],check=True)
    return 0

if __name__=='__main__':raise SystemExit(main())
