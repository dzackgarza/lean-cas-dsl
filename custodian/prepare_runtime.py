#!/usr/bin/env python3
"""Build a minimal credential-free Docker runtime from installed system Python.

This is a trusted setup operation, never an author tool. Copies only the selected
installed interpreter, its stdlib and linked libraries. Reports an immutable image
identity for trusted launcher configuration; it grants no acceptance.
"""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import tempfile


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--python',type=Path,required=True)
    args=parser.parse_args()
    python=args.python.resolve()
    stdlib=Path(subprocess.run([str(python),'-c','import sysconfig; print(sysconfig.get_path("stdlib"))'],check=True,capture_output=True,text=True).stdout.strip())
    shared=set()
    for binary in (python,*stdlib.glob('lib-dynload/*.so')):
        result=subprocess.run(['ldd',str(binary)],check=True,capture_output=True,text=True)
        for found in re.findall(r'(/[^\s]+)',result.stdout):
            path=Path(found)
            if path.is_file():shared.add(path)
    with tempfile.TemporaryDirectory(prefix='custodian-runtime-') as tmp:
        root=Path(tmp)/'root';root.mkdir()
        for path in {python,stdlib}|shared:
            dest=root/str(path).lstrip('/');dest.parent.mkdir(parents=True,exist_ok=True)
            if path.is_dir():shutil.copytree(path,dest,dirs_exist_ok=True)
            else:shutil.copy2(path,dest,follow_symlinks=True)
        (root/'tmp').mkdir()
        for path in root.rglob('*'):
            path.chmod(0o755 if path.is_dir() or '.so' in path.name or path==root/str(python).lstrip('/') else 0o644)
        archive=Path(tmp)/'runtime.tar'
        with tarfile.open(archive,'w') as tar:
            for path in root.iterdir():tar.add(path,arcname=path.name)
        result=subprocess.run(['docker','import','--change',f'ENTRYPOINT ["{python}"]',str(archive),'custodian-python:local'],check=True,capture_output=True,text=True)
        print(result.stdout.strip())
    return 0

if __name__=='__main__':raise SystemExit(main())
