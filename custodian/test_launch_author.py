"""Inspect the actual fresh-author launch invocation; fake CLI is transport only."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

class AuthorLaunchTest(unittest.TestCase):
    def test_only_role_mcp_and_independent_assignment(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);binary=root/'bin';binary.mkdir();capture=root/'capture.json'
            fake=binary/'claude'
            fake.write_text('#!/usr/bin/env python3\nimport json,pathlib,sys,os\na=sys.argv[1:]; m=json.loads(pathlib.Path(a[a.index("--mcp-config")+1]).read_text()); pathlib.Path('+repr(str(capture))+').write_text(json.dumps({"args":a,"mcp":m,"assignment":sys.stdin.read(),"cwd":os.getcwd()}))\n')
            fake.chmod(0o755)
            config=root/'config.json';config.write_text(json.dumps({'source_repository':str(root/'source'),'independently_supplied_assignment':'fixture independently supplied requirement'}))
            env=dict(os.environ,PATH=str(binary)+os.pathsep+os.environ['PATH'])
            command=['python3',str(Path(__file__).with_name('launch_author.py')),'--configuration',str(config)]
            subprocess.run(command,env=env,check=True,capture_output=True)
            value=json.loads(capture.read_text());args=value['args']
            self.assertIn('--restricted',args);self.assertIn('--strict-mcp-config',args)
            self.assertEqual(args[args.index('--tools')+1],'')
            self.assertEqual(args[args.index('--setting-sources')+1],'')
            self.assertEqual(value['assignment'],'fixture independently supplied requirement')
            self.assertEqual(list(value['mcp']['mcpServers']),['role_source'])
            allowed=args[args.index('--allowedTools')+1].split(',')
            self.assertEqual(set(allowed),{'mcp__role_source__'+x for x in ('read_assigned_input','read_source','list_source','write_source','submit_source')})
            self.assertFalse(Path(value['cwd']).exists(),'temporary inference cwd removed')
            config.write_text(json.dumps({'source_repository':str(root/'source')}))
            self.assertNotEqual(subprocess.run(command,env=env,capture_output=True).returncode,0)

if __name__=='__main__':unittest.main()
