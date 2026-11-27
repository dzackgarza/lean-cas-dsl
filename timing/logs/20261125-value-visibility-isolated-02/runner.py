from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess,sys,time,traceback
stage=Path(__file__).resolve().parent
repo=stage.parents[1]
record=repo/'timing/logs/20261125-value-visibility-isolated-02'
def stamp(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def save(name,value):
 path=stage/name
 temp=path.with_name(path.name+'.pending')
 temp.write_text(json.dumps(value,indent=2)+'\n')
 temp.replace(path)
 shutil.copy2(path,record/name)
manifest=json.loads((stage/'snapshot.json').read_text())
state={'started_utc':stamp(),'runner_pid':os.getpid(),'modules':[],'status':'running'}
save('status.json',state)
try:
 for relative,expected in manifest['staged_sources'].items():
  assert sha(stage/relative)==expected, f'staged input changed: {relative}'
 env=os.environ.copy()
 env['LEAN_PATH']=str(stage/'artifacts')+os.pathsep+env.get('LEAN_PATH','')
 env['CAS_APPLICATION_LOG_DIR']=str(stage/'application')
 env['CAS_FEEDBACK_RUN']='isolated-value-visibility-20261125-02'
 state['lake_environment']={key:env.get(key) for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','PATH','CAS_APPLICATION_LOG_DIR']}
 for module in manifest['modules']:
  name=module.split('.')[-1]
  source=stage/'src'/Path(*module.split('.')).with_suffix('.lean')
  target=stage/'artifacts'/Path(*module.split('.'))
  command=['lean','--root='+str(stage/'src'),str(source),'-o',str(target)+'.olean','-i',str(target)+'.ilean','-c',str(target)+'.c']
  module_log=stage/'logs'/f'{name}.log'
  item={'module':module,'command':command,'started_utc':stamp(),'log':str(module_log.relative_to(stage))}
  state['modules'].append(item)
  with module_log.open('wb') as output:
   process=subprocess.Popen(command,cwd=repo,env=env,stdin=subprocess.DEVNULL,stdout=output,stderr=subprocess.STDOUT)
   item['pid']=process.pid
   save('status.json',state)
   print(json.dumps({'module':module,'pid':process.pid,'log':str(module_log)}),flush=True)
   start=time.monotonic()
   item['exit_code']=process.wait()
   item['seconds']=round(time.monotonic()-start,3)
  item['finished_utc']=stamp()
  shutil.copy2(module_log,record/'logs'/module_log.name)
  save('status.json',state)
  print(json.dumps(item),flush=True)
  if item['exit_code']!=0:
   state['status']='failed'
   break
 else:
  state['status']='passed'
 live_changes=[relative for relative,expected in manifest['unchanged_namespace_artifacts'].items() if not (repo/relative).exists() or sha(repo/relative)!=expected]
 state['live_namespace_artifact_changes']=live_changes
 if live_changes:
  state['status']='failed'
  state['isolation_error']='live namespace artifacts changed during isolated validation'
 for relative,expected in manifest['staged_sources'].items():
  assert sha(stage/relative)==expected, f'staged input changed after execution: {relative}'
 for relative,expected in manifest['source_inputs'].items():
  assert sha(repo/relative)==expected, f'live source changed: {relative}'
except BaseException as exc:
 state['status']='error'
 state['exception']=repr(exc)
 traceback.print_exc()
finally:
 state['finished_utc']=stamp()
 shutil.copytree(stage/'application',record/'application',dirs_exist_ok=True)
 save('status.json',state)
 save('result.json',state)
print(json.dumps({'status':state['status'],'result':str(stage/'result.json')}),flush=True)
sys.exit(0 if state['status']=='passed' else 1)
