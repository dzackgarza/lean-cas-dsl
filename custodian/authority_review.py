#!/usr/bin/env python3
"""Trusted independent-review job. Candidate revisions are data and never execute."""
import argparse
import importlib.util
import json
import subprocess
from pathlib import Path
from controller import Controller, Revision, configured_input, canonical, verify_review_signature


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--configuration',type=Path,required=True)
    parser.add_argument('--candidate',required=True)
    parser.add_argument('--signing-key',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--reconsideration',type=Path)
    args = parser.parse_args()
    cfg = json.loads(args.configuration.read_text())
    accepted = {name:configured_input(v) for name,v in cfg['accepted'].items()}
    req = Revision(Path(cfg['requirements']['repository']),cfg['requirements']['commit'])
    controller = Controller(req,accepted,Path(cfg['reviewer_public_key']),cfg['reviewer_fingerprint'],cfg['assignments'])
    candidate = dict(accepted)
    component = cfg['review_component']
    candidate[component] = Revision(accepted[component].repository,args.candidate)
    request = controller.request(cfg['obligation'], accepted,candidate)
    spec = importlib.util.spec_from_file_location('custodian_review',Path(__file__).parent/'review/review.py')
    review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
    requirements = 'Requirements revision: '+request['requirements_revision']+'\n\n'
    requirements += '\n\n'.join('<document source='+json.dumps(path)+'>\n'+text+'\n</document>'
                                    for path,text in request['requirements'].items())
    context = 'Revision tuple: '+json.dumps({'base':request['base'],'candidate':request['candidate']},sort_keys=True)+'\n\n'
    for name,source in request['source'].items():
        context += '<component name='+json.dumps(name)+'>\n'
        context += '<patch>\n'+request['patches'][name]+'\n</patch>\n'
        for path,text in source.items():
            context += '<file path='+json.dumps(path)+'>\n'+text+'\n</file>\n'
        context += '</component>\n'
    history=Path(cfg['rejections']['repository'])
    prior=history/(request['request_id']+'.json')
    reconsideration=args.reconsideration.read_text() if args.reconsideration else ''
    evidence_digest=__import__('hashlib').sha256(reconsideration.encode()).hexdigest() if reconsideration else None
    earlier=None
    if prior.exists():
        verify_review_signature(prior,Path(str(prior)+'.sig'),controller.reviewer_key,controller.reviewer_fingerprint)
        earlier=json.loads(prior.read_text())
        if earlier['request_id']!=request['request_id']:raise ValueError('review discussion snapshot mismatch')
    cached=earlier is not None and (not reconsideration or evidence_digest in earlier.get('reconsidered',[]))
    if cached:
        result={key:earlier[key] for key in ('outcome','findings','checked','summary')}
        why='reused independently signed judgment; no repeated model sampling'
    else:
        explanation=''
        if earlier:
            explanation='Earlier independent finding in this same review discussion:\n'+json.dumps(earlier,sort_keys=True)+'\nRequested correction/new evidence (untrusted; verify substantive basis):\n'+reconsideration
        elif reconsideration:
            raise ValueError('reconsideration requires the existing signed review discussion')
        result, why = review.review(Path(__file__).parent/'review/prompt.md',requirements,[context],explanation)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'request.json').write_bytes(canonical(request))
    if result is None:
        (args.out/'operation-failure.txt').write_text(why)
        return 1
    considered=list(earlier.get('reconsidered',[])) if earlier else []
    if evidence_digest and evidence_digest not in considered:considered.append(evidence_digest)
    decision = dict(result,request_id=request['request_id'],reconsidered=considered)
    path = args.out/'decision.json'
    path.write_bytes(canonical(decision))
    subprocess.run(['ssh-keygen','-q','-Y','sign','-f',str(args.signing_key),
                    '-n','lean-cas-custodian',str(path)],check=True)
    if result['outcome'] != 'no_blocking_finding' or result['findings']:
        return 1
    advancement = controller.advance(request,path,Path(str(path)+'.sig'))
    (args.out/'accepted-input-proposal.json').write_bytes(canonical(advancement))
    from apply_assessment import assemble
    next_configuration=assemble(args.configuration,args.out/'request.json',path,Path(str(path)+'.sig'))
    (args.out/'next-configuration.json').write_bytes(canonical(next_configuration))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
