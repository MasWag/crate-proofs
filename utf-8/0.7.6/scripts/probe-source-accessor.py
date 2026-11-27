#!/usr/bin/env python3
"""Probe faithful inherited Error::source observer; output is diagnostic only."""
import sys, pathlib,json,subprocess,tempfile
root=pathlib.Path(__file__).resolve().parents[1];repo=root.parents[1];sys.path.insert(0,str(repo/'scripts'))
from aeneas_management import tools
lock,key=tools.identity(root/'aeneas/profiles/default');env=tools.environment(repo/'.work/tools'/key,lock);env.update(RUSTUP_TOOLCHAIN=lock['extraction_rust'],CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(root/'.work/build/boundary-probes'))
(root/'.work/boundary-probes').mkdir(parents=True,exist_ok=True)
run=pathlib.Path(tempfile.mkdtemp(prefix='methods-',dir=root/'.work/boundary-probes'));print(run,flush=True)
for label,flags in [('bool',[]),('optimized',['--mir','optimized']),('mono',['--monomorphize']),('opt4',['--mir','optimized','--rustc-arg=-Zmir-opt-level=4'])]:
 d=run/label;d.mkdir();args=['charon','cargo','--preset=aeneas','--start-from','crate::decode_error_source_is_none','--include','core::error::Error::source','--remove-unused-clauses',*flags,'--dest-file',str(d/'Utf8SourceAccessor.llbc'),'--','--lib','--locked','--offline']
 with (d/'charon.log').open('w') as f:r=subprocess.run(args,cwd=root/'verification/source-accessor',env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode==0:
  with (d/'aeneas.log').open('w') as f:r=subprocess.run(['aeneas','-backend','lean','-dest',str(d),str(d/'Utf8SourceAccessor.llbc')],cwd=root/'verification/source-accessor',env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode == 0 and (d/'Utf8SourceAccessor.lean').exists():
  with (d/'lean.log').open('w') as f:
   subprocess.run(['lake','env','lean',str(d/'Utf8SourceAccessor.lean')],cwd=root/'.work/selected-proofs',env=env,stdout=f,stderr=subprocess.STDOUT)
 (d/'command.json').write_text(json.dumps(args,indent=2)+'\n')
 print(label,r.returncode,flush=True)
