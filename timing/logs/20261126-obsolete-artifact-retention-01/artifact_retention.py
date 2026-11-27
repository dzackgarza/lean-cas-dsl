from pathlib import Path
from decimal import Decimal
import base64,datetime,hashlib,json,os,shutil,stat,subprocess,sys,tarfile
ROOT=Path.cwd().resolve()
OUT=ROOT/'timing/logs/20261126-obsolete-artifact-retention-01'
ALLOWED={
 'context-batch-01':'.tmp/validation-context-batch-20261125-01/artifacts',
 'value-visibility-01':'.tmp/validation-value-visibility-20261125-01/artifacts',
 'value-visibility-02':'.tmp/validation-value-visibility-20261125-02/artifacts',
 'binding-application-phases-01':'.tmp/validation-binding-application-phases-20261125-01/artifacts'}
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(name,data):
 p=OUT/name
 with p.open('x') as f:json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def digest(path):
 h=hashlib.sha256()
 fd=os.open(path,os.O_RDONLY|os.O_NOATIME)
 with os.fdopen(fd,'rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def metadata(path):
 s=path.lstat()
 assert stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode),(str(path),'unexpected special file')
 assert stat.S_ISDIR(s.st_mode) or s.st_nlink==1,(str(path),'multiply linked file')
 data={'type':'directory' if stat.S_ISDIR(s.st_mode) else 'file','mode':stat.S_IMODE(s.st_mode),'uid':s.st_uid,'gid':s.st_gid,'size':s.st_size,'mtime_ns':s.st_mtime_ns,'atime_ns':s.st_atime_ns,'ctime_ns':s.st_ctime_ns,'device':s.st_dev,'inode':s.st_ino,'nlink':s.st_nlink,'blocks':s.st_blocks,'xattrs':{k:base64.b64encode(os.getxattr(path,k,follow_symlinks=False)).decode() for k in sorted(os.listxattr(path,follow_symlinks=False))}}
 if data['type']=='file':data['sha256']=digest(path)
 return data
def capture(label):
 source=ROOT/ALLOWED[label]
 assert source.is_dir() and source.resolve()==source and not source.is_symlink()
 return {str(p.relative_to(ROOT)):metadata(p) for p in [source,*sorted(source.rglob('*'))]}
def path_users(label):
 relative=ALLOWED[label]
 prefixes=[str(ROOT/relative),'/home/dzack/.local/share/docker/volumes/sage-repos/_data/v1-integration-20261106/lean-cas-dsl/'+relative,'/repos/v1-integration-20261106/lean-cas-dsl/'+relative,relative]
 matches=[];native=[];denied=[]
 for q in Path('/proc').iterdir():
  if not q.name.isdigit() or int(q.name)==os.getpid():continue
  try:
   comm=(q/'comm').read_text().strip();argv=(q/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace');cwd=os.readlink(q/'cwd')
   if comm in ['lean','lake'] and cwd in [str(ROOT),'/repos/v1-integration-20261106/lean-cas-dsl']:native.append({'pid':int(q.name),'comm':comm,'argv':argv,'cwd':cwd})
   sources=[('argv',argv),('cwd',cwd)]
   for item in (q/'environ').read_bytes().split(b'\0'):
    if item.startswith((b'LEAN_PATH=',b'LEAN_SRC_PATH=')):sources.append(('lean_environment',item.decode(errors='replace')))
   for fd in (q/'fd').iterdir():
    try:sources.append(('fd',os.readlink(fd)))
    except FileNotFoundError:pass
   sources.append(('maps',(q/'maps').read_text(errors='replace')))
   found=sorted({kind for kind,value in sources if any(prefix in value for prefix in prefixes)})
   if found:matches.append({'pid':int(q.name),'comm':comm,'references':found})
  except FileNotFoundError:pass
  except PermissionError:denied.append(int(q.name))
 record={'utc':now(),'path':relative,'matches':matches,'active_native':native,'inaccessible_processes':denied}
 assert not matches and not native,record
 return record
def verify_archive(label,manifest):
 archive=OUT/(label+'.tar.zst');seen=set();xattrs=0
 proc=subprocess.Popen(['zstd','--decompress','--stdout','--quiet',str(archive)],stdout=subprocess.PIPE)
 try:
  with tarfile.open(fileobj=proc.stdout,mode='r|') as tar:
   for member in tar:
    name=member.name.rstrip('/');assert name in manifest and name not in seen,name;seen.add(name);expected=manifest[name]
    assert (member.isdir() if expected['type']=='directory' else member.isfile()),name
    assert (member.mode,member.uid,member.gid)==(expected['mode'],expected['uid'],expected['gid']),name
    assert int(Decimal(member.pax_headers.get('mtime',str(member.mtime)))*1000000000)==expected['mtime_ns'],name
    for key,value in expected['xattrs'].items():
     actual=member.pax_headers['SCHILY.xattr.'+key].encode('utf-8','surrogateescape');assert base64.b64encode(actual).decode()==value,(name,key);xattrs+=1
    if expected['type']=='file':
     assert member.size==expected['size'],name
     h=hashlib.sha256();f=tar.extractfile(member)
     for block in iter(lambda:f.read(1048576),b''):h.update(block)
     assert h.hexdigest()==expected['sha256'],name
  assert proc.wait()==0
 except BaseException:
  proc.stdout.close();proc.wait();raise
 assert seen==set(manifest)
 return {'verified_utc':now(),'archive_sha256':digest(archive),'archive_bytes':archive.stat().st_size,'members':len(seen),'file_count':sum(m['type']=='file' for m in manifest.values()),'logical_file_bytes':sum(m['size'] for m in manifest.values() if m['type']=='file'),'verified_xattrs':xattrs,'verified_fields':['type','mode','uid','gid','mtime_ns','xattrs','size','sha256'],'additional_original_metadata_retained_in_manifest':['atime_ns','ctime_ns','device','inode','nlink','blocks']}
def archive(label):
 before=path_users(label);manifest=capture(label);write(label+'.manifest.json',{'created_utc':now(),'root':str(ROOT),'relative_root':ALLOWED[label],'entries':manifest})
 archive=OUT/(label+'.tar.zst');assert not archive.exists()
 command=['tar','--create','--file',str(archive),'--format=pax','--acls','--xattrs','--xattrs-include=*','--selinux','--numeric-owner','--atime-preserve=system','--use-compress-program=zstd -T1 -6','--',ALLOWED[label]]
 with (OUT/(label+'.archive.log')).open('xb') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
 with archive.open('rb') as f:os.fsync(f.fileno())
 proof=verify_archive(label,manifest)
 current=capture(label);assert current==manifest,'Source changed during archive'
 proof.update({'label':label,'original_path':str(ROOT/ALLOWED[label]),'archive_path':str(archive),'manifest_sha256':digest(OUT/(label+'.manifest.json')),'command':command,'process_exclusion_before':before,'process_exclusion_after':path_users(label),'original_tree_unchanged':True,'retired':False,'free_bytes':shutil.disk_usage(ROOT).free})
 write(label+'.archive-verification.json',proof);print(json.dumps(proof),flush=True)
def retire(label):
 proof=json.loads((OUT/(label+'.archive-verification.json')).read_text());manifest=json.loads((OUT/(label+'.manifest.json')).read_text())['entries']
 assert digest(OUT/(label+'.manifest.json'))==proof['manifest_sha256']
 assert digest(OUT/(label+'.tar.zst'))==proof['archive_sha256']
 assert capture(label)==manifest,'Source changed since verification'
 exclusion=path_users(label);before=shutil.disk_usage(ROOT).free
 source=ROOT/ALLOWED[label];assert source.resolve()==source and source.parent.name.startswith('validation-') and source.name=='artifacts'
 shutil.rmtree(source)
 assert not source.exists();after=shutil.disk_usage(ROOT).free
 result={'retired_utc':now(),'label':label,'original_path':str(source),'archive_path':proof['archive_path'],'archive_sha256':proof['archive_sha256'],'manifest_sha256':proof['manifest_sha256'],'verified_members':proof['members'],'verified_file_count':proof['file_count'],'original_logical_bytes':proof['logical_file_bytes'],'archive_bytes':proof['archive_bytes'],'original_allocated_blocks_bytes':sum(x['blocks']*512 for x in manifest.values()),'free_bytes_before':before,'free_bytes_after':after,'observed_free_bytes_increase':after-before,'process_exclusion':exclusion,'retired':True,'restoration':'Verify archive and manifest SHA256, extract from repository root with GNU tar --zstd --extract --file ARCHIVE --same-owner --same-permissions --acls --xattrs --xattrs-include=* --selinux; restore recorded atime_ns/mtime_ns from manifest. Kernel inode/device/ctime identities cannot be recreated but their exact original values are retained.'}
 write(label+'.retirement.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':
 action,label=sys.argv[1:];assert label in ALLOWED
 if action=='archive':archive(label)
 elif action=='retire':retire(label)
 else:raise ValueError(action)
