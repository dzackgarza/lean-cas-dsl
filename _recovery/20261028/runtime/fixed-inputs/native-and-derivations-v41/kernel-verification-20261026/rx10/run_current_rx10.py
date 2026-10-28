"""Freeze and run the fixed RX10 engineering driver at an explicitly compiled producer."""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path
ROOT=Path(os.environ.get('CAS_KERNEL_WORKTREE', str(Path('/workspace/scratch/c3e234b1b92d/lean-cas-dsl'))))
OUT=Path('/workspace/scratch/c3e234b1b92d/kernel-verification-20261026/rx10')
WRAPPER=Path('/workspace/scratch/c3e234b1b92d/kernel-runtime-20261026/lake.sh')
PACKAGES=Path('/workspace/scratch/c3e234b1b92d/kernel-runtime-20261026/packages.json')
PLAN=Path('/workspace/scratch/c3e234b1b92d/kernel-verification-20261026/rx10/historical-plan.json')

def run_git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def digest(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
 return h.hexdigest()
def info(p):
 p=Path(p)
 return {'path':str(p),'resolved_path':str(p.resolve()),'sha256':digest(p),'bytes':p.stat().st_size}
def git_state(path):
 result={}
 for key,args in [('commit',['rev-parse','HEAD']),('tree',['rev-parse','HEAD^{tree}']),('status',['status','--short'])]:
  completed=subprocess.run(['git',*args],cwd=path,text=True,capture_output=True)
  result[key]=completed.stdout.strip() if completed.returncode==0 else {'unavailable':completed.stderr.strip()}
 return result

ap=argparse.ArgumentParser()
ap.add_argument('producer'); ap.add_argument('name'); ap.add_argument('manifest')
ap.add_argument('--build-provenance',required=True)
ap.add_argument('--execution-plan',required=True)
a=ap.parse_args()
producer=run_git('rev-parse',a.producer).decode().strip()
build_path=Path(a.build_provenance)
build=json.loads(build_path.read_text())
if build.get('status')!='completed' or build.get('exit')!=0 or build.get('sourceTupleChanged'):
 raise SystemExit('A successful unchanged-source consumer build is required')
if build['producer']['kernel']['commit']!=producer or git_state(ROOT)['commit']!=producer:
 raise SystemExit('The selected producer differs from the current successful build/source')
build_sources_before={}
for name,selected in build['producer'].items():
 current=git_state(selected['path'])
 if current['commit']!=selected['commit'] or current['tree']!=selected['tree'] or current['status']:
  raise SystemExit('A selected build input changed before execution')
 build_sources_before[name]=current
execution_plan=Path(a.execution_plan).resolve()
selected_plan=json.loads(execution_plan.read_text())
leaves_before={name:git_state(row['path']) for name,row in selected_plan['leaves'].items()}
for name,row in selected_plan['leaves'].items():
 current=leaves_before[name]
 if current['commit']!=row['commit'] or current['tree']!=row['tree'] or current['status']:
  raise SystemExit('A frozen leaf source changed: '+name)
manifest_record=info(a.manifest)
if not any(Path(group['manifest']['path']).resolve()==Path(a.manifest).resolve() and
           group['manifest']['sha256']==manifest_record['sha256']
           for group in selected_plan['groups'].values()):
 raise SystemExit('The manifest is not the exact selected execution-plan manifest')
folder=OUT/a.name
folder.mkdir()
source_dir=folder/'source'; source_dir.mkdir()
source_path='CasAcceptance/Kernel/FixedQuestionExecutionControls.lean'
driver=source_dir/'FixedQuestionExecutionControls.lean'
driver.write_bytes(run_git('show',producer+':'+source_path)); driver.chmod(0o444)
fixtures=source_dir/'Strata'; fixtures.mkdir()
fixture_paths=run_git('ls-tree','-r','--name-only',producer,'CasAcceptance/Strata').decode().splitlines()
for relative in fixture_paths:
 if relative.endswith('.py'):
  dest=fixtures/Path(relative).name
  dest.write_bytes(run_git('show',producer+':'+relative)); dest.chmod(0o444)
packages=json.loads(PACKAGES.read_text())
package_roots={p['name']:Path(p['dir']) for p in packages['packages'] if p.get('type')=='path'}
roots={'CasCatalogue':ROOT,'CasTools':ROOT,'CasAcceptance':ROOT,
       'LeanCategories':package_roots['lean_categories'],
       'CasContract':package_roots['cas_leaf_contracts']}
paths=set()
setups={}
modules=set(re.findall(r'(?m)^(?:(?:public|meta)\s+)*import\s+(\S+)',driver.read_text()))
for module in sorted(modules):
 root=roots.get(module.split('.',1)[0])
 if root is None: raise RuntimeError('Unexpected direct import namespace: '+module)
 relative=Path(*module.split('.'))
 setup=root/'.lake/build/ir'/relative.with_suffix('.setup.json')
 if not setup.is_file(): raise RuntimeError('Missing current import setup: '+str(setup))
 setups[str(setup)]=info(setup)
 imported=set(json.loads(setup.read_text()).get('importArts',{}))|{module}
 for name in imported:
  imported_root=roots.get(name.split('.',1)[0])
  if imported_root is None: continue
  imported_relative=Path(*name.split('.'))
  for suffix in ['.olean','.olean.private','.olean.server','.ir','.ir.sig']:
   path=imported_root/'.lake/build/lib/lean'/Path(str(imported_relative)+suffix)
   if path.exists(): paths.add(path)
  if not (imported_root/'.lake/build/lib/lean'/imported_relative.with_suffix('.olean')).exists():
   raise RuntimeError('Missing current imported module: '+name)
artifacts={str(p):info(p) for p in sorted(paths)}
for runtime_path in [WRAPPER.parent/'lean-4.33.0-linux/lib/lean/Init.olean',
                     WRAPPER.parent/'lean-4.33.0-linux/bin/lean']:
 artifacts[str(runtime_path)]=info(runtime_path)
raw=folder/'conditions.json'
log=folder/'run.log'
env=os.environ.copy()
env.update({'LEAN_NUM_THREADS':'1','CAS_KERNEL_SOURCE':str(ROOT),
            'CAS_FROZEN_LEAF_MANIFEST':str(Path(a.manifest).resolve()),
            'CAS_FIXED_QUESTION_REPORT':str(raw),'CAS_CONDITION_PROTOCOL_DIR':str(fixtures)})
env.pop('CAS_EXTENSION_CONTROL',None); env.pop('CAS_EXTENSION_CONTROL_REPORT',None)
command=['bash',str(WRAPPER),'env','lean',str(driver)]
fixed_input=ROOT/'tests/acceptance/proposals/independent-extension-reconstruction-20261024/completion/rx10-fixed-execution-question.cas'
report={'producer':{'commit':producer,'tree':run_git('rev-parse',producer+'^{tree}').decode().strip()},
 'root_at_start':git_state(ROOT),'mathematics':git_state(roots['LeanCategories']),
 'contract':git_state(roots['CasContract']),'packages':info(PACKAGES),'wrapper':info(WRAPPER),
 'engines':info('/workspace/scratch/c3e234b1b92d/computational-runtime-20261026/engines.sh'),'driver':info(driver),
 'original_source':source_path,'fixtures':[info(p) for p in sorted(fixtures.iterdir())],
 'manifest':manifest_record,'fixed_input':info(fixed_input),
 'execution_plan':info(execution_plan),'leaves_before':leaves_before,
 'build_sources_before':build_sources_before,
 'artifacts_before':artifacts,'current_import_setups':setups,
 'artifact_inventory_note':'Each direct driver import uses its current compiled setup closure, resolved through the selected source roots. New transitive modules are included; no historical artifact inventory is reused.',
 'original_preparation_plan':info(PLAN),'runner':info(__file__),
 'successful_consumer_build':info(build_path),'consumer_build_log':info(build['log']['path']),
 'command':command,'environment':{k:env.get(k) for k in ['LEAN_NUM_THREADS','CAS_KERNEL_SOURCE','CAS_SAGE_PYTHON','CAS_GAP_PYTHON','CAS_LEAF_CONTRACT_PATH','PYTHONPATH','CAS_FROZEN_LEAF_MANIFEST','CAS_FIXED_QUESTION_REPORT','CAS_CONDITION_PROTOCOL_DIR']},
 'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
(folder/'report.json').write_text(json.dumps(report,indent=2)+'\n')
started=time.monotonic()
with log.open('x') as stream: finished=subprocess.run(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
report.update({'exit':finished.returncode,'seconds':round(time.monotonic()-started,3),'log':info(log),
 'artifact_changes':[],'setup_changes':[],'fixed_input_after':info(fixed_input),'raw':info(raw) if raw.exists() else {'exists':False},
 'root_at_end':git_state(ROOT),'mathematics_at_end':git_state(roots['LeanCategories']),
 'contract_at_end':git_state(roots['CasContract'])})
report['build_sources_after']={name:git_state(row['path']) for name,row in build['producer'].items()}
report['leaves_after']={name:git_state(row['path']) for name,row in selected_plan['leaves'].items()}
report['manifest_after']=info(a.manifest)
report['execution_plan_after']=info(execution_plan)
for path,before in artifacts.items():
 after=info(path)
 if after['sha256']!=before['sha256']:report['artifact_changes'].append({'before':before,'after':after})
for path,before in setups.items():
 after=info(path)
 if after['sha256']!=before['sha256']:report['setup_changes'].append({'before':before,'after':after})
report['source_changes']=[name for name,before,after in [
 ('kernel',report['root_at_start'],report['root_at_end']),
 ('mathematics',report['mathematics'],report['mathematics_at_end']),
 ('contract',report['contract'],report['contract_at_end'])] if before!=after]
report['source_changes'] += ['build dependency '+name for name,before in build_sources_before.items()
                              if before!=report['build_sources_after'][name]]
report['source_changes'] += ['leaf '+name for name,before in leaves_before.items()
                              if before!=report['leaves_after'][name]]
report['input_changes']=[key for key in ['manifest','execution_plan','fixed_input']
                         if report[key]['sha256']!=report[key+'_after']['sha256']]
if raw.exists():
 result=json.loads(raw.read_text())
 report['observations_summary']=[{'condition':v.get('condition'),'kind':v.get('kind'),
   'detail':v.get('detail'),'dispatches':len(v.get('dispatches',[])),
   'callableReused':v.get('callableReused'),
   'sameIndependentTypedQuestion':v.get('sameIndependentTypedQuestion'),
   'sessionControls':({k:v['sessionControls'].get(k) for k in
    ['kind','detail','foreignKind','expiredKind','freshKind','originalOwner','foreignOwner','freshOwner']}
    if isinstance(v.get('sessionControls'),dict) else v.get('sessionControls'))}
  for v in result.get('observations',[])]
(folder/'report.json').write_text(json.dumps(report,indent=2)+'\n')
summary={k:report.get(k) for k in ['producer','exit','seconds','artifact_changes','setup_changes','source_changes','input_changes','observations_summary']}
summary['report']=info(folder/'report.json')
print(json.dumps(summary,indent=2),flush=True)
print(log.read_text()[:22000],flush=True)
raise SystemExit(finished.returncode or bool(report['artifact_changes'] or report['setup_changes'] or report['source_changes'] or report['input_changes']))
