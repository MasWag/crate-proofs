#!/usr/bin/env python3
"""Validate pinned compiler, model bytes, prelude and read-only prover installation."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
    raise RuntimeError('Python optimization is forbidden for tool checks')
def sha(p):
    with Path(p).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def tree(p):
    p=Path(p);items={str(f.relative_to(p)):sha(f) for f in sorted(p.rglob('*'))
        if f.is_file() and not any(x in ('.git','target') for x in f.relative_to(p).parts)}
    return hashlib.sha256(json.dumps(items,sort_keys=True).encode()).hexdigest()
def command(args,cwd=None):return subprocess.check_output(args,cwd=cwd,text=True,stderr=subprocess.DEVNULL).strip()
def snapshot():
    work=Path(os.environ.get('CREUSOT_OPTION_WORK',ROOT/'.work'))
    data=Path(os.environ.get('CREUSOT_DATA_HOME',work/'data'))
    tools=work/'tools/creusot'
    assert command(['git','-C',str(tools),'rev-parse','HEAD'])=='318615be3b8bbc60d1f6d52469ba5c0bdebed4f1'
    assert not command(['git','-C',str(tools),'status','--porcelain','--untracked-files=no'])
    exe={'cargo-creusot':work/'cargo/bin/cargo-creusot',
         'creusot-rustc':data/'toolchains/nightly-2026-06-22/bin/creusot-rustc',
         'why3':data/'bin/why3','why3find':data/'bin/why3find','z3':data/'bin/z3'}
    prefix=(data/'bin/why3').resolve().parents[1]
    info={'binaries_sha256':{n:sha(p) for n,p in exe.items()},
          'rustc_sha256':sha(Path(command(['rustup','run','nightly-2026-06-22','rustc','--print','sysroot']))/'bin/rustc'),
          'native_rustc_sha256':sha(Path(command(['rustup','run','1.94.1','rustc','--print','sysroot']))/'bin/rustc'),
          'native_rustc_version':command(['rustup','run','1.94.1','rustc','--version']),
          'rustc_version':command(['rustup','run','nightly-2026-06-22','rustc','--version']),
          'why3_version':command([str(exe['why3']),'--version']),
          'why3find_version':command([str(exe['why3find']),'--version']),
          'z3_version':command([str(exe['z3']),'--version']),
          'why3_runtime_sha256':tree(prefix/'lib/why3'),
          'why3find_runtime_sha256':tree(prefix/'lib/why3find'),
          'prelude_sha256':tree(data/'share/why3find/packages/creusot'),
          'prover_config_sha256':sha(data/'creusot_why3.conf')}
    metadata=json.loads(command(['cargo','metadata','--locked','--offline','--format-version','1','--manifest-path',str(ROOT/'Cargo.toml')],'/private/tmp'))
    models={}
    for p in metadata['packages']:
        if p['name'] not in ('creusot-std','creusot-std-proc','pearlite-syn'):continue
        assert p['version']=='0.13.0'
        assert p['source'].endswith('#318615be3b8bbc60d1f6d52469ba5c0bdebed4f1')
        src=Path(p['manifest_path']).parent
        assert tree(src)==tree(tools/p['name']), 'Active Git model differs from compiler source'
        models[p['name']]={'version':p['version'],'source':p['source'],'tree_sha256':tree(src)}
    assert len(models)==3
    info['active_model_packages']=models
    return info
if __name__=='__main__':
    actual=snapshot();expected=json.loads((ROOT/'toolchain.lock.json').read_text())['observed_tools']
    assert actual==expected,'Pinned tool/model mismatch; inspect actual environment before accepting proof'
    print(json.dumps(actual,indent=2,sort_keys=True))
