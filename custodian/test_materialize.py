import json
from pathlib import Path
import subprocess
import tempfile
import unittest

class MaterializeTest(unittest.TestCase):
    def test_one_revision_tuple_retrieved_without_candidate_execution(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);source=root/'source';source.mkdir()
            def git(*args):return subprocess.run(['git','-C',str(source),*args],check=True,capture_output=True,text=True).stdout.strip()
            git('init','-q');git('config','user.name','fixture');git('config','user.email','fixture@example.test')
            (source/'candidate.py').write_text('raise RuntimeError("candidate must not execute")')
            git('add','.');git('commit','-qm','source')
            commit=git('rev-parse','HEAD');dest=root/'inputs'
            entry={'repository':str(dest),'url':str(source),'commit':commit}
            config=root/'config.json';config.write_text(json.dumps({'requirements':entry,'accepted':{'acceptance':entry},'review_component':'acceptance'}))
            subprocess.run(['python3',str(Path(__file__).with_name('materialize.py')),'--configuration',str(config),'--candidate',commit],check=True,capture_output=True)
            self.assertFalse((dest/'candidate.py').exists())
            value=subprocess.run(['git','-C',str(dest),'show',commit+':candidate.py'],check=True,capture_output=True,text=True).stdout
            self.assertIn('candidate must not execute',value)

if __name__=='__main__':unittest.main()
