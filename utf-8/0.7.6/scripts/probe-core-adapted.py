#!/usr/bin/env python3
"""Reproduce adapted core extraction with the unchanged default pinned tools."""
import json, subprocess, sys, tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; REPO=ROOT.parents[1]
sys.path.insert(0,str(REPO/'scripts'))
from aeneas_management import tools
lock,key=tools.identity(ROOT/'aeneas/profiles/default')
store=REPO/'.work/tools'/key;tools.check(store,lock)
env=tools.environment(store,lock)
parent=ROOT/'.work/core-adapted';parent.mkdir(parents=True,exist_ok=True)
run=Path(tempfile.mkdtemp(prefix='run-',dir=parent));source=run/'source'
env.update(RUSTUP_TOOLCHAIN=lock['extraction_rust'],CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(run/'target'))
subprocess.run([sys.executable,str(ROOT/'scripts/prepare-core-adapted.py'),str(source)],check=True)
with (run/'lock.log').open('w') as f:subprocess.run(['cargo','generate-lockfile','--offline'],cwd=source,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
command=[sys.executable,str(REPO/'scripts/aeneas-extract.py'),str(source),'--config',str(ROOT/'aeneas/profiles/core_adapted/extraction.json'),'--output',str(run/'generated')]
with (run/'driver.log').open('w') as f:result=subprocess.run(command,env=env,stdout=f,stderr=subprocess.STDOUT)
(run/'result.json').write_text(json.dumps({'command':command,'exit_code':result.returncode,'scope':'classification-conditional adapted helper extraction only'},indent=2)+'\n')
print(run);sys.exit(result.returncode)
