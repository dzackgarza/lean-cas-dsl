#!/usr/bin/env python3
"""Restore an exact official Lean release, without building kernel sources."""
import hashlib, json, pathlib, subprocess, time
ROOT = pathlib.Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
RECEIPT = EVIDENCE / "toolchain-bootstrap.json"
METADATA = EVIDENCE / "lean-4.33.0-release.json"
metadata = json.loads(METADATA.read_text())
asset, = [a for a in metadata["assets"] if a["name"] == "lean-4.33.0-linux.tar.zst"]
expected = "4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c"
assert metadata["tag_name"] == "v4.33.0"
assert asset["digest"] == "sha256:" + expected
ARCHIVES = ROOT / "archives"
TOOLCHAINS = ROOT / "toolchains"
ARCHIVES.mkdir(exist_ok=True)
TOOLCHAINS.mkdir(exist_ok=True)
archive = ARCHIVES / asset["name"]
toolchain = TOOLCHAINS / "lean-4.33.0-linux"
started = time.time()
receipt = {"purpose":"Restore official pinned compiler only; no kernel or guarded verification", "sourceMetadata":str(METADATA), "sourceMetadataSha256":hashlib.sha256(METADATA.read_bytes()).hexdigest(), "asset":{k:asset[k] for k in ("name", "id", "size", "digest", "browser_download_url")}, "started":started, "status":"running"}
def save():
 RECEIPT.write_text(json.dumps(receipt,indent=2) + "\n")
save()
try:
 if not archive.exists():
  temporary = archive.with_suffix(archive.suffix + ".part")
  with (EVIDENCE / "toolchain-download.log").open("w") as log:
   subprocess.run(["curl", "--fail", "--location", "--retry", "2", "--output", str(temporary), asset["browser_download_url"]], stdout=log, stderr=subprocess.STDOUT, check=True)
  temporary.rename(archive)
 h=hashlib.sha256()
 with archive.open("rb") as f:
  for block in iter(lambda:f.read(8*1024*1024), b""):
   h.update(block)
 receipt["archive"] = str(archive)
 receipt["actualBytes"] = archive.stat().st_size
 receipt["actualSha256"] = h.hexdigest()
 assert receipt["actualBytes"] == asset["size"]
 assert receipt["actualSha256"] == expected
 if not toolchain.exists():
  members = subprocess.run(["tar", "--zstd", "-tf", str(archive)],check=True,text=True,capture_output=True).stdout.splitlines()
  assert members and all(m.startswith("lean-4.33.0-linux/") and ".." not in pathlib.PurePosixPath(m).parts for m in members)
  with (EVIDENCE / "toolchain-extraction.log").open("w") as log:
   subprocess.run(["tar", "--zstd", "-xf", str(archive), "-C", str(TOOLCHAINS)], stdout=log,stderr=subprocess.STDOUT,check=True)
 versions={}
 for name in ("lean", "lake"):
  binary=toolchain/"bin"/name
  result=subprocess.run([str(binary),"--version"],check=True,text=True,capture_output=True)
  versions[name] = result.stdout.strip()
  if name == "lean":
   assert "4.33.0" in result.stdout and "d8b1897" in result.stdout
 receipt.update(status="completed", toolchain=str(toolchain), versions=versions, elapsedSeconds=time.time()-started)
 save()
 print(json.dumps(receipt,indent=2))
except BaseException as exc:
 receipt.update(status="failed", error=repr(exc), elapsedSeconds=time.time()-started)
 save()
 raise
