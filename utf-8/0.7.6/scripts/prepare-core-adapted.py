#!/usr/bin/env python3
"""Prepare a fresh derived release input; never mutate the locked source tree."""
import argparse, hashlib, json, shutil, subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser();p.add_argument('destination',type=Path);args=p.parse_args()
source=root/'.work/source'; dest=args.destination.absolute()
import sys
sys.path.insert(0,str(root.parents[1]/'scripts'))
from aeneas_management import source as source_management
if source.is_symlink(): raise SystemExit('release source directory must not be a symlink')
source_management.check(source,json.loads((root/'source.lock.json').read_text()))
if dest.is_symlink() or any(p.is_symlink() for p in dest.parents):
    raise SystemExit('destination path must not contain symlinks')
if dest.exists(): raise SystemExit('destination must be new')
shutil.copytree(source,dest)
patch=root/'aeneas/profiles/core_adapted/source.patch'
subprocess.run(['patch','-p1','-i',str(patch)],cwd=dest,check=True)
with (dest/'Cargo.toml').open('a') as f:f.write('\n[workspace]\n')
manifest={'release_lib_sha256':hashlib.sha256((source/'src/lib.rs').read_bytes()).hexdigest(),'adapted_lib_sha256':hashlib.sha256((dest/'src/lib.rs').read_bytes()).hexdigest(),'patch_sha256':hashlib.sha256(patch.read_bytes()).hexdigest(),'domain':'buffer_len <= 4; classifier relation required separately'}
(dest/'adaptation.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(dest)
