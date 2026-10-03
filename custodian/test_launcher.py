import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from controller import Controller, Revision, ExternalArtifact
from launcher import RoleServer

class LauncherTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.repo = self.root/'source'; self.repo.mkdir()
        self.shell('git','init','-q',str(self.repo))
        self.shell('git','-C',str(self.repo),'config','user.name','test')
        self.shell('git','-C',str(self.repo),'config','user.email','test@example.test')
        for path in ('INTENT.md','specs/architecture.md','specs/computational-core-plan.md','specs/owner/convergence-process.md'):
            p=self.repo/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text('`b0-authority` full fixed requirements')
        self.commit()
        self.revision=Revision(self.repo,self.shell('git','-C',str(self.repo),'rev-parse','HEAD'))
    def tearDown(self): self.tmp.cleanup()
    def shell(self,*args): return subprocess.run(args,check=True,capture_output=True,text=True).stdout.strip()
    def commit(self):
        self.shell('git','-C',str(self.repo),'add','.')
        self.shell('git','-C',str(self.repo),'commit','-qm','source')
    def server(self,role):
        c=Controller(self.revision,dict.fromkeys(('mathematics','contract','acceptance','public_metadata'),self.revision),self.root/'unused-key','unused-fingerprint',{'b0-authority':role})
        return RoleServer(c,'b0-authority',self.repo)
    def test_authority_operations_absent_for_every_role(self):
        for role in ('kernel','formalization','acceptance','leaf'):
            server=self.server(role)
            self.assertEqual({t['name'] for t in server.tools()},{'read_assigned_input','read_source','list_source','write_source','submit_source'})
            for operation in ('commission_formalization','approve','publish','advance','assign','execute'):
                with self.assertRaises(PermissionError): server.call(operation,{})
            for path in ('custodian/root.pub','custodian/controller.py','.github/workflows/trusted.yml','specs/owner/convergence-process.md','INTENT.md','scripts/check_acceptance.py'):
                with self.assertRaises(PermissionError): server.call('write_source',{'path':path,'content':'forged authority'})
    def test_leaf_receives_frozen_public_artifact_without_mathematics_or_acceptance(self):
        import hashlib
        artifact=self.root/'external-public.json';artifact.write_text('{"operation":"declared"}')
        public=ExternalArtifact.load(self.revision,artifact,hashlib.sha256(artifact.read_bytes()).hexdigest(),{'mathematics':self.revision.commit,'contract':self.revision.commit})
        c=Controller(self.revision,{'contract':self.revision,'public_metadata':public},self.root/'unused-key','unused',{'b0-authority':'leaf'})
        server=RoleServer(c,'b0-authority',self.repo)
        self.assertEqual(set(server.inputs),{'contract','public_metadata'})
        artifact.write_text('changed after dispatch')
        self.assertEqual(server.call('read_assigned_input',{'input':'public_metadata','path':'public_operation_metadata.json'}),'{"operation":"declared"}')
        with self.assertRaises(ValueError):server.call('read_assigned_input',{'input':'public_metadata','path':'INTENT.md'})
        with self.assertRaises(KeyError):server.call('read_assigned_input',{'input':'acceptance','path':'anything'})

    def test_real_write_read_checkpoint_submission_flow_without_shell_capability(self):
        server=self.server('kernel')
        server.call('write_source',{'path':'CasCatalogue/Work.py','content':'complete source'})
        self.assertEqual(server.call('read_source',{'path':'CasCatalogue/Work.py'}),'complete source')
        self.assertIn('CasCatalogue/Work.py',json.loads(server.call('list_source',{})))
        submission=json.loads(server.call('submit_source',{}))
        self.assertEqual(submission['kind'],'source_submission')
        self.assertEqual(submission['changed_paths'],['CasCatalogue/Work.py'])
        self.assertEqual(self.shell('git','-C',str(self.repo),'show',submission['candidate']+':CasCatalogue/Work.py'),'complete source')
        self.assertEqual(self.shell('git','-C',str(self.repo),'status','--porcelain'),'')

    def test_noncanonical_path_spellings_never_write_protected_source(self):
        server=self.server('kernel')
        for path in ('custodian/controller.py','tests/acceptance/admitted.json','LeanCategories/Meaning.lean','AGENTS.md'):
            target=self.repo/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_text('protected original')
            variants=('./'+path,path.replace('/', '//'),path.replace('/', '/./'),path+'/')
            for variant in variants:
                with self.assertRaises(PermissionError):server.call('write_source',{'path':variant,'content':'forged'})
                self.assertEqual(target.read_text(),'protected original')
        with self.assertRaises(PermissionError):server.call('write_source',{'path':'CasCatalogue/../custodian/controller.py','content':'forged'})

    def test_hostile_authority_submission_refused(self):
        (self.repo/'custodian').mkdir()
        (self.repo/'custodian/root.pub').write_text('candidate key')
        self.commit()
        commit=self.shell('git','-C',str(self.repo),'rev-parse','HEAD')
        for role in ('kernel','formalization','acceptance','leaf'):
            with self.assertRaises(PermissionError): self.server(role).call('submit_source',{'candidate':commit})
    def test_kernel_source_and_unrelated_failure_do_not_need_review(self):
        server=self.server('kernel')
        server.call('write_source',{'path':'CasCatalogue/Kernel.py','content':'source'})
        # No review credentials or decision are supplied for source construction.
        self.assertEqual((self.repo/'CasCatalogue/Kernel.py').read_text(),'source')
        with self.assertRaises(PermissionError): server.call('write_source',{'path':'LeanCategories/Meaning.lean','content':'changed'})
    def test_links_and_traversal_cannot_escape_source_endpoint(self):
        server=self.server('kernel')
        outside=self.root/'outside';outside.mkdir()
        (self.repo/'linked').symlink_to(outside,target_is_directory=True)
        for path in ('linked/secret','../outside/secret','/tmp/secret'):
            with self.assertRaises(PermissionError):server.call('write_source',{'path':path,'content':'changed'})
        self.assertFalse((outside/'secret').exists())
        protected=self.repo/'custodian';protected.mkdir()
        (protected/'controller.py').write_text('protected original')
        (self.repo/'alias').symlink_to(protected,target_is_directory=True)
        for operation,args in (('write_source',{'path':'alias/controller.py','content':'forged'}),('read_source',{'path':'alias/controller.py'})):
            with self.assertRaises(PermissionError):server.call(operation,args)
        self.assertEqual((protected/'controller.py').read_text(),'protected original')
    def test_stdio_tool_exposure_uses_launcher_assignment(self):
        cfg={'requirements':{'repository':str(self.repo),'commit':self.revision.commit},
             'accepted':{name:{'repository':str(self.repo),'commit':self.revision.commit} for name in ('mathematics','contract','acceptance')},
             'reviewer_public_key':str(self.root/'unused-key'),'reviewer_fingerprint':'unused',
             'assignments':{'b0-authority':'acceptance'},'obligation':'b0-authority','source_repository':str(self.repo)}
        config=self.root/'launch.json';config.write_text(json.dumps(cfg))
        requests=[{'jsonrpc':'2.0','id':1,'method':'tools/list'},
                  {'jsonrpc':'2.0','id':2,'method':'tools/call','params':{'name':'write_source','arguments':{'path':'CasCatalogue/Forbidden','content':'x'}}}]
        result=subprocess.run(['python3',str(Path(__file__).with_name('launcher.py')),'--configuration',str(config)],input='\n'.join(map(json.dumps,requests))+'\n',capture_output=True,text=True,check=True)
        responses=list(map(json.loads,result.stdout.splitlines()))
        self.assertIn('error',responses[1])
        inputs=responses[0]['result']['tools'][0]['inputSchema']['properties']['input']['enum']
        self.assertEqual(set(inputs),{'mathematics','contract'})

if __name__=='__main__': unittest.main()
