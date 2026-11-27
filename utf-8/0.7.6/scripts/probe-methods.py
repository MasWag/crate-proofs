#!/usr/bin/env python3
import sys, pathlib,json,subprocess,tempfile
# Diagnostic only. Never promote partial output or opaque application declarations.
root=pathlib.Path(__file__).resolve().parents[1];repo=root.parents[1];sys.path.insert(0,str(repo/'scripts'))
from aeneas_management import tools
lock,key=tools.identity(root/'aeneas/profiles/default');env=tools.environment(repo/'.work/tools'/key,lock);env.update(RUSTUP_TOOLCHAIN=lock['extraction_rust'],CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(root/'.work/build/boundary-probes'))
(root/'.work/boundary-probes').mkdir(parents=True,exist_ok=True)
run=pathlib.Path(tempfile.mkdtemp(prefix='methods-',dir=root/'.work/boundary-probes'));print(run,flush=True)
entries=['crate::lossy::LossyDecoder::new','crate::read::BufReadDecoder::new','crate::read::BufReadDecoderError::lossy','{impl core::ops::drop::Drop for crate::lossy::LossyDecoder}::drop','{impl core::clone::Clone for crate::Incomplete}::clone','{impl core::clone::Clone for crate::DecodeError}::clone','{impl core::error::Error for crate::read::BufReadDecoderError}::source','{impl core::fmt::Display for crate::DecodeError}::fmt','{impl core::fmt::Debug for crate::Incomplete}::fmt','{impl core::fmt::Debug for crate::DecodeError}::fmt','{impl core::fmt::Debug for crate::read::BufReadDecoderError}::fmt','{impl core::fmt::Display for crate::read::BufReadDecoderError}::fmt','crate::read::BufReadDecoder::next_lossy','crate::read::BufReadDecoder::read_to_string_lossy']
entries += ['{impl core::error::Error for crate::DecodeError}::source', 'core::error::Error::source']
results = {}
for i,e in enumerate(entries):
 d=run/str(i);d.mkdir();args=['charon','cargo','--preset=aeneas','--start-from',e,'--include','core::error::Error::source','--remove-unused-clauses','--dest-file',str(d/'Utf8.llbc'),'--','--lib','--locked','--offline'];(d/'entry.json').write_text(json.dumps(args));
 with (d/'charon.log').open('w') as f:r=subprocess.run(args,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 if r.returncode==0:
  with (d/'aeneas.log').open('w') as f:r=subprocess.run(['aeneas','-backend','lean','-dest',str(d),str(d/'Utf8.llbc')],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 results[str(i)] = {'entry':e, 'charon_command':args, 'exit_code':r.returncode}
 if (d/'Utf8.lean').exists():
  text=(d/'Utf8.lean').read_text()
  results[str(i)]['contains_axiom'] = any(line.startswith('axiom ') for line in text.splitlines())
  if r.returncode == 0 and not results[str(i)]['contains_axiom']:
   with (d/'lean.log').open('w') as f:
    c=subprocess.run(['lake','env','lean',str(d/'Utf8.lean')],cwd=root/'.work/selected-proofs',env=env,stdout=f,stderr=subprocess.STDOUT)
   results[str(i)]['lean_exit_code']=c.returncode
 print(i,e,r.returncode,flush=True)
(run/'results.json').write_text(json.dumps(results,indent=2)+'\n')
