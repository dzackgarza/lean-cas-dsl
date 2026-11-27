from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
run=Path('timing/logs/20261126-source-tuple-domain-83')
command=['just','probe','.tmp/source-tuple-domain-20261126/MatrixDomainProbe.lean']
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
started=now();clock=time.monotonic()
with (run/'environment-dependencies.log').open('xb') as metadata_log:
 subprocess.run([sys.executable,str(run/'capture-environment-dependencies.py')],stdout=metadata_log,stderr=subprocess.STDOUT,check=True)
context={'started_utc':started,'cwd':str(Path.cwd()),'command':command,'diagnostic_only':True,'wrapper_pid':os.getpid(),'environment':{k:os.environ.get(k) for k in ['CAS_LEAVES','PATH','LEAN_PATH','LEAN_SYSROOT','CAS_APPLICATION_LOG_DIR']},'lean_toolchain':Path('lean-toolchain').read_text().strip(),'probe_sha256':hashlib.sha256(Path(command[2]).read_bytes()).hexdigest()}
(run/'context.json').write_text(json.dumps(context,indent=2)+'\n')
with (run/'output.log').open('xb') as log:
 proc=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (run/'process.json').write_text(json.dumps({'wrapper_pid':os.getpid(),'child_pid':proc.pid,'started_utc':started},indent=2)+'\n')
 for block in iter(proc.stdout.readline,b''):
  log.write(block);log.flush();sys.stdout.buffer.write(block);sys.stdout.buffer.flush()
 status=proc.wait()
result={'command':command,'diagnostic_only':True,'started_utc':started,'finished_utc':now(),'seconds':time.monotonic()-clock,'status':status,'probe_sha256':context['probe_sha256'],'output_sha256':hashlib.sha256((run/'output.log').read_bytes()).hexdigest(),'acceptance_status':None}
(run/'result.json').write_text(json.dumps(result,indent=2)+'\n')
print('DIAGNOSTIC_RESULT '+json.dumps(result),flush=True)
raise SystemExit(status)
