"""Trusted assembly/signature/publication preparation; model is explicitly a fixture."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from controller import Controller, Revision, canonical
from apply_assessment import assemble
from verify_publication import verify

class AssessmentTest(unittest.TestCase):
    def test_complete_assessment_cache_and_protected_publication_draft(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);repo=root/'source';repo.mkdir();history=root/'history';history.mkdir()
            def run(*args,**kw):return subprocess.run(args,check=True,capture_output=True,text=True,**kw).stdout.strip()
            run('git','init','-q',str(repo));run('git','-C',str(repo),'config','user.name','fixture');run('git','-C',str(repo),'config','user.email','fixture@example.test')
            for path in ('SPEC.md','INTENT.md','specs/architecture.md','specs/computational-core-plan.md','specs/owner/convergence-process.md','tests/acceptance/question.txt'):
                p=repo/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('`b0-authority` fixed fixture requirements\n')
            run('git','-C',str(repo),'add','.');run('git','-C',str(repo),'commit','-qm','base');base=run('git','-C',str(repo),'rev-parse','HEAD')
            (repo/'tests/acceptance/question.txt').write_text('independent source proposal\n')
            run('git','-C',str(repo),'add','.');run('git','-C',str(repo),'commit','-qm','proposal');candidate=run('git','-C',str(repo),'rev-parse','HEAD')
            key=root/'test-review-key';run('ssh-keygen','-q','-t','ed25519','-N','','-f',str(key));fingerprint=run('ssh-keygen','-lf',str(key)+'.pub').split()[1]
            remote=root/'history.git';run('git','init','--bare','-q',str(remote));run('git','init','-q',str(history));run('git','-C',str(history),'remote','add','origin',str(remote))
            cfg={'requirements':{'repository':str(repo),'commit':base},'accepted':{name:{'repository':str(repo),'commit':base} for name in ('mathematics','contract','acceptance')},'reviewer_public_key':str(key)+'.pub','reviewer_fingerprint':fingerprint,'assignments':{'b0-authority':'acceptance'},'obligation':'b0-authority','review_component':'acceptance','rejections':{'repository':str(history),'ref':'custodian/rejections'}}
            artifact=root/'public-metadata.json';artifact.write_text('immutable fixture public metadata')
            cfg['accepted']['public_metadata']={'repository':str(root/'unavailable-upstream-checkout'),'commit':base,'artifact_file':str(artifact),'sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'provenance':{'mathematics':base,'contract':base}}
            config=root/'config.json';config.write_text(json.dumps(cfg))
            binary=root/'bin';binary.mkdir();calls=root/'calls'
            fake=binary/'claude';fake.write_text('#!/usr/bin/env python3\nimport json,pathlib,sys\npathlib.Path('+repr(str(calls))+').write_text("called")\njson.dump({"subtype":"success","structured_output":{"outcome":"no_blocking_finding","findings":[],"checked":["fixture transport"],"summary":"fixture; not independent technical assessment"}},sys.stdout)\n');fake.chmod(0o755)
            env=dict(os.environ,PATH=str(binary)+os.pathsep+os.environ['PATH'])
            out=root/'out'
            command=['python3',str(Path(__file__).with_name('authority_review.py')),'--configuration',str(config),'--candidate',candidate,'--signing-key',str(key),'--out',str(out)]
            run(*command,env=env)
            self.assertTrue(calls.exists())
            result=assemble(config,out/'request.json',out/'decision.json',out/'decision.json.sig')
            self.assertEqual(result['accepted']['acceptance']['commit'],candidate)
            request=json.loads((out/'request.json').read_text());requestid=request['request_id']
            publication=root/'publication';proof=publication/'custodian/admission'/requestid;proof.mkdir(parents=True)
            (publication/'custodian/deployment.json').write_text(json.dumps(result))
            with self.assertRaises(ValueError):verify(config,publication)
            for name in ('request.json','decision.json','decision.json.sig'):(proof/name).write_bytes((out/name).read_bytes())
            verify(config,publication)
            altered=dict(result);altered['obligation']='candidate invented authority'
            (publication/'custodian/deployment.json').write_text(json.dumps(altered))
            with self.assertRaises(ValueError):verify(config,publication)
            record=['python3',str(Path(__file__).with_name('record_review.py')),'--configuration',str(config),'--out',str(out)]
            run(*record)
            first_record=run('git','-C',str(remote),'rev-parse','refs/heads/custodian/rejections')
            run(*record)
            self.assertEqual(first_record,run('git','-C',str(remote),'rev-parse','refs/heads/custodian/rejections'))
            self.assertEqual(json.loads(run('git','-C',str(remote),'show','custodian/rejections:'+requestid+'.json'))['request_id'],requestid)
            calls.unlink();second=root/'out-second'
            run(*command[:-1],str(second),env=env)
            self.assertFalse(calls.exists(),'identical review cannot sample another model judgment')
            draft=json.loads(run('python3',str(Path(__file__).with_name('publish_assessment.py')),'--configuration',str(config),'--request',str(out/'request.json'),'--decision',str(out/'decision.json'),'--signature',str(out/'decision.json.sig'),'--deployment-repository',str(repo)))
            self.assertEqual(draft['base'],'accepted/controller')
            self.assertEqual(draft['request_id'],requestid)
            self.assertEqual(run('git','-C',str(repo),'status','--porcelain'),'')
            # Changing signed context, even with the same claimed immutable identities, fails.
            request['source']['acceptance']['tests/acceptance/question.txt']='forged content'
            request['request_id']=hashlib.sha256(canonical({k:v for k,v in request.items() if k!='request_id'})).hexdigest()
            (out/'request.json').write_text(json.dumps(request))
            with self.assertRaises(ValueError):assemble(config,out/'request.json',out/'decision.json',out/'decision.json.sig')

if __name__=='__main__':unittest.main()
