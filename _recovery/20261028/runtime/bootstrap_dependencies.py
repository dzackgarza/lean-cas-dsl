import concurrent.futures,hashlib,json,os,pathlib,subprocess,time
runtime=pathlib.Path(__file__).resolve().parent
root=pathlib.Path('/workspace/scratch/4e9256f8ceed/lean-cas-dsl-kernel')
evidence=runtime/'evidence';evidence.mkdir(exist_ok=True)
manifest=root/'lake-manifest.json'; original=manifest.read_bytes(); data=json.loads(original)
selected=[]
def restore(row):
 name=row['name']; revision=row['rev']; directory=runtime/'dependencies'/name
 if directory.exists(): raise RuntimeError('Refuse to replace existing dependency '+str(directory))
 if len(revision)!=40 or any(c not in '0123456789abcdef' for c in revision):raise RuntimeError('Unpinned dependency')
 if pathlib.Path(name).name!=name or name in ['.','..']:raise RuntimeError('Unsafe dependency name')
 directory.parent.mkdir(exist_ok=True)
 log=evidence/('fetch-'+name+'.log')
 with log.open('x') as stream:
  for command in [['git','init',str(directory)],['git','-C',str(directory),'remote','add','origin',row['url']],['git','-C',str(directory),'fetch','--depth','1','origin',revision],['git','-C',str(directory),'checkout','--detach','FETCH_HEAD']]:
   subprocess.run(command,check=True,stdout=stream,stderr=subprocess.STDOUT,env={**os.environ,'GIT_TERMINAL_PROMPT':'0'})
 def git(*args):return subprocess.check_output(['git','--no-optional-locks','-C',str(directory),*args],text=True).strip()
 actual=git('rev-parse','HEAD')
 if actual!=revision:raise RuntimeError('Revision mismatch '+name)
 subdir=pathlib.Path(row.get('subDir') or '.')
 if subdir.is_absolute() or '..' in subdir.parts:raise RuntimeError('Unsafe subdirectory')
 package=directory/subdir
 if not (package/row['configFile']).is_file():raise RuntimeError('Missing selected configuration')
 record={'name':name,'repository':row['url'],'root':str(directory),'dir':str(package),'commit':actual,'tree':git('rev-parse','HEAD^{tree}'),'status':git('status','--porcelain'),'log':str(log)}
 print(json.dumps({'restored':name,'commit':actual}),flush=True)
 override={'name':name,'dir':str(package),'type':'path',**{key:row[key] for key in ['inherited','scope','configFile','manifestFile']}}
 return record,override
started=time.time()
report={'purpose':'Dependency source bootstrap only; no kernel or guarded verification','manifest':str(manifest),'manifestSha256':hashlib.sha256(original).hexdigest(),'kernelAtStart':subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip(),'started':started,'sources':[],'status':'running'}
receipt=evidence/'dependency-bootstrap.json';receipt.write_text(json.dumps(report,indent=2)+'\n')
try:
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
  restored=list(pool.map(restore,data['packages']))
 (runtime/'packages.json').write_text(json.dumps({'schemaVersion':'1.2.0','packages':[p for _,p in restored]},indent=2)+'\n')
 report.update(status='completed',sources=[r for r,_ in restored],elapsedSeconds=time.time()-started,manifestUnchanged=manifest.read_bytes()==original)
except BaseException as error:
 report.update(status='failed',error=repr(error),elapsedSeconds=time.time()-started)
 receipt.write_text(json.dumps(report,indent=2)+'\n');raise
receipt.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'sources':len(report['sources']),'receipt':str(receipt)}),flush=True)
