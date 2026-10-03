#!/usr/bin/env python3
"""Assemble a protected-publication change from an independently signed assessment.

Only the trusted launcher/operator invokes this. It verifies the exact immutable
request again and emits the next configuration for publication to the protected
accepted-input reference. It neither publishes nor changes a worker's status.
"""
import argparse
import json
from pathlib import Path
from controller import Controller, Revision, configured_input, canonical


def assemble(configuration, request, decision, signature):
    cfg=json.loads(configuration.read_text())
    accepted={name:configured_input(value) for name,value in cfg['accepted'].items()}
    req=Revision(Path(cfg['requirements']['repository']),cfg['requirements']['commit'])
    controller=Controller(req,accepted,Path(cfg['reviewer_public_key']),cfg['reviewer_fingerprint'],cfg['assignments'])
    envelope=json.loads(request.read_text())
    advancement=controller.advance(envelope,decision,signature)
    result=json.loads(json.dumps(cfg))
    for name,value in advancement.items():
        if isinstance(value,str):result['accepted'][name]['commit']=value
        else:result['accepted'][name].update(value)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('configuration','request','decision','signature','out'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    result=assemble(args.configuration,args.request,args.decision,args.signature)
    # Avoid replacing any existing user configuration during source preparation.
    with args.out.open('xb') as output:output.write(canonical(result))
    return 0

if __name__=='__main__':raise SystemExit(main())
