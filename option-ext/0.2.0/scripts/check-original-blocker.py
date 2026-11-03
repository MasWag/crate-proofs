#!/usr/bin/env python3
"""Reproduce the original-body translation failure; never accept its partial Lean."""
import hashlib, json, os, subprocess, sys, tempfile
from pathlib import Path
root = Path(__file__).resolve().parents[1]
repo = root.parents[1]
base = root/'.work/blockers'; base.mkdir(parents=True,exist_ok=True)
run = Path(tempfile.mkdtemp(prefix='original-nullary-',dir=base))
out = run/'generated'
config = root/'aeneas/profiles/default/extraction-original-all.json'
cmd = [sys.executable,str(repo/'scripts/aeneas-extract.py'),str(root),'--config',str(config),'--output',str(out)]
with (run/'driver.log').open('w') as log:
    env = dict(os.environ, RUSTUP_TOOLCHAIN='nightly-2026-09-17')
    result = subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,env=env)
assert result.returncode != 0, 'Original boundary changed; review newly successful extraction'
log = (out/'aeneas.log').read_text()
assert 'Found unexpected constant: ()' in log
assert 'map_or_else' in log
assert 'Generated the partial file' in log
record = {'status':'expected-original-body-extraction-blocker','command':cmd,'returncode':result.returncode,'config_sha256':hashlib.sha256(config.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256((out/'aeneas.log').read_bytes()).hexdigest(),'limitation':'This failure does not prove a Rust defect or correctness; partial Lean is never admitted to maintained proofs.'}
(run/'result.json').write_text(json.dumps(record,indent=2)+'\n')
print('Original map_or_else2 translation blocker reproduced:',run)
