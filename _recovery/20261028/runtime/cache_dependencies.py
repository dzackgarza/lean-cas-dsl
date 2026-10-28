#!/usr/bin/env python3
"""Bootstrap dependency cache; never compile kernel/contract/mathematics-owner sources."""
import hashlib, json, os, pathlib, re, shlex, shutil, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
KERNEL=ROOT.parents[1]/"lean-cas-dsl-kernel"
EVIDENCE=ROOT/"evidence"
SELECTED={row["name"]:pathlib.Path(row["dir"]) for row in json.loads((ROOT/"packages.json").read_text())["packages"]}
MATHLIB=SELECTED["mathlib"]
TOOLCHAIN=ROOT/"toolchains/lean-4.33.0-linux"
ENV=dict(os.environ, GIT_OPTIONAL_LOCKS="0", GIT_TERMINAL_PROMPT="0", PATH=str(TOOLCHAIN/"bin")+os.pathsep+os.environ["PATH"], MATHLIB_CACHE_DIR=str(ROOT/"mathlib-cache"))
def git(root,*args):
 return subprocess.check_output(["git","--no-optional-locks","-C",str(root),*args],env=ENV,text=True).strip()
def sha(data): return hashlib.sha256(data).hexdigest()
def state():
 return {name:{"dir":str(root),"commit":git(root,"rev-parse","HEAD"),"tree":git(root,"rev-parse","HEAD^{tree}"),"status":git(root,"status","--porcelain")} for name,root in SELECTED.items()}
revision=git(KERNEL,"rev-parse","HEAD")
paths=subprocess.check_output(["git","-C",str(KERNEL),"ls-tree","-r","--name-only",revision],text=True).splitlines()
paths=[p for p in paths if p.endswith(".lean") and p.split("/")[0].startswith("Cas")]
objects=[revision+":"+p for p in paths]
process=subprocess.run(["git","-C",str(KERNEL),"cat-file","--batch"],input="\n".join(objects).encode()+b"\n",check=True,capture_output=True)
stream=memoryview(process.stdout); offset=0; frozen={}
for path in paths:
 end=process.stdout.index(b"\n",offset); header=bytes(stream[offset:end]).decode().split(); size=int(header[2]); offset=end+1
 frozen[path]=bytes(stream[offset:offset+size]).decode(); offset+=size+1
prefixes={"Mathlib","Aesop","Qq","Batteries","ProofWidgets","LeanSearchClient","ImportGraph","Plausible"}
pattern=re.compile(r"^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z_][A-Za-z_0-9.]*)\s*$",re.M)
seen={}; targets=set()
def visit(identifier,source):
 if identifier in seen:return
 seen[identifier]=sha(source.encode())
 for module in pattern.findall(source):
  if module.split(".")[0] in prefixes:
   targets.add(module);continue
  relative=module.replace(".","/")+".lean"
  if relative in frozen:
   visit("kernel@"+revision+":"+relative,frozen[relative]);continue
  for name,base in SELECTED.items():
   path=base/relative
   if path.is_file():
    visit(name+":"+relative,path.read_text());break
for path,source in frozen.items():visit("kernel@"+revision+":"+path,source)
inputs={"purpose":"Published source imports select a dependency cache only; this is not kernel verification", "kernelReadRevision":revision,"sourceFiles":len(seen),"sourceHashes":seen,"modules":sorted(targets)}
(EVIDENCE/"cache-inputs.json").write_text(json.dumps(inputs,indent=2)+"\n")
started=time.time(); identifier=str(time.time_ns()); receiptPath=EVIDENCE/("dependency-cache-"+identifier+".json"); logPath=receiptPath.with_suffix(".log")
command=[str(TOOLCHAIN/"bin/lake"),"--packages="+str(ROOT/"packages.json"),"exe","cache","get",*sorted(targets)]
receipt={"purpose":"Restore mathematical dependency artifacts only; no kernel or guarded verification", "started":started,"status":"running","cwd":str(MATHLIB),"command":command,"sourceSelectionBefore":state(),"requestInputs":str(EVIDENCE/"cache-inputs.json"),"requestInputsSha256":sha((EVIDENCE/"cache-inputs.json").read_bytes()),"packagesSha256":sha((ROOT/"packages.json").read_bytes()),"log":str(logPath)}
receiptPath.write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps({"receipt":str(receiptPath),"requestedModules":len(targets),"sourceFiles":len(seen)}),flush=True)
try:
 with logPath.open("x") as log:
  result=subprocess.run(command,cwd=MATHLIB,env=ENV,stdout=log,stderr=subprocess.STDOUT)
 receipt["cacheExit"]=result.returncode
 if result.returncode: raise RuntimeError("Dependency cache command failed")
 relocations=[]; extracted=MATHLIB/".lake/packages"; backup=ROOT/("cache-extraction-originals-"+identifier);backup.mkdir()
 for package in extracted.iterdir() if extracted.exists() else []:
  if package.is_symlink():continue
  if sorted(item.name for item in package.iterdir()) != [".lake"] or package.name not in SELECTED:
   raise RuntimeError("Unexpected extracted package: "+str(package))
  destination=SELECTED[package.name]
  shutil.copytree(package/".lake",destination/".lake",dirs_exist_ok=True)
  original=backup/package.name; package.rename(original);package.symlink_to(destination,target_is_directory=True)
  relocations.append({"package":package.name,"original":str(original),"selected":str(destination)})
 receipt["relocations"]=relocations
 receipt["sourceSelectionAfter"]=state()
 receipt["sourceSelectionChanged"]=receipt["sourceSelectionBefore"]!=receipt["sourceSelectionAfter"]
 if receipt["sourceSelectionChanged"]:raise RuntimeError("Dependency source changed during cache bootstrap")
 receipt.update(status="completed", elapsedSeconds=time.time()-started)
except BaseException as exc:
 receipt.update(status="failed", error=repr(exc), elapsedSeconds=time.time()-started)
 raise
finally:
 receipt["logSha256"]=sha(logPath.read_bytes()) if logPath.exists() else None
 receiptPath.write_text(json.dumps(receipt,indent=2)+"\n")
 print(json.dumps({k:receipt.get(k) for k in ("status","cacheExit","elapsedSeconds","error")}),flush=True)
