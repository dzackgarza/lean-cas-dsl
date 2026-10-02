"""Actual container privilege probes, separate from mathematical acceptance."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from controller import Revision
from execution import execute

class ExecutionTest(unittest.TestCase):
    def test_actual_candidate_has_no_authority_credentials_mounts_or_network(self):
        image=subprocess.run(['docker','image','inspect','custodian-python:local','--format','{{.Id}}'],check=True,capture_output=True,text=True).stdout.strip()
        with tempfile.TemporaryDirectory() as tmp:
            repo=Path(tmp)/'repo';repo.mkdir()
            def git(*args):return subprocess.run(['git','-C',str(repo),*args],check=True,capture_output=True,text=True).stdout.strip()
            git('init','-q');git('config','user.name','test');git('config','user.email','test@example.test')
            (repo/'probe.py').write_text('''import json, os, pathlib, socket
report = {"uid":os.getuid(), "authority_env":any(k in os.environ for k in ("GH_TOKEN","GITHUB_TOKEN","CUSTODIAN_REVIEW_KEY","CLAUDE_CODE_OAUTH_TOKEN")), "host_mount":pathlib.Path("/workspace").exists(), "git_metadata":pathlib.Path("/candidate/.git").exists(), "docker_socket":pathlib.Path("/var/run/docker.sock").exists()}
try:
 pathlib.Path("/candidate/forged").write_text("authority")
 report["source_writable"] = True
except OSError: report["source_writable"] = False
try:
 socket.create_connection(("1.1.1.1",443),timeout=1)
 report["network"] = True
except OSError: report["network"] = False
print(json.dumps(report))
''')
            git('add','.');git('commit','-qm','probe')
            revision=Revision(repo,git('rev-parse','HEAD'))
            observation=execute(revision,image,('/candidate/probe.py',))
            self.assertEqual(observation['returncode'],0,observation['stderr'])
            result=json.loads(observation['stdout'])
            self.assertEqual(result,{'uid':65534,'authority_env':False,'host_mount':False,'git_metadata':False,'docker_socket':False,'source_writable':False,'network':False})
            with self.assertRaises(ValueError):execute(revision,'mutable:tag',('/candidate/probe.py',))
            timed = execute(revision,image,('-c','while True: pass'),timeout=0.2)
            self.assertEqual(timed['operation_failure'],'process_timeout')
            self.assertNotEqual(subprocess.run(['docker','container','inspect',timed['container']],capture_output=True).returncode,0)
            noisy = execute(revision,image,('-c','while True: print("x"*10000, flush=True)'),output_limit=4096)
            self.assertEqual(noisy['operation_failure'],'output_limit')
            self.assertLessEqual(len(noisy['stdout'].encode())+len(noisy['stderr'].encode()),4096)
            self.assertNotEqual(subprocess.run(['docker','container','inspect',noisy['container']],capture_output=True).returncode,0)

if __name__=='__main__':unittest.main()
