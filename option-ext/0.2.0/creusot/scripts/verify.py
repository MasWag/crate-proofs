#!/usr/bin/env python3
"""Fresh standard Creusot run with complete positive-root and identity checks."""
import sys,re
import datetime,importlib.util,json,os,shutil,subprocess,tempfile,xml.etree.ElementTree as ET
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE','') not in ('','0'):
    raise RuntimeError('Python optimization is forbidden for evidence checks')
overrides={'RUSTC','RUSTDOC','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','RUSTFLAGS',
 'CARGO_ENCODED_RUSTFLAGS','CARGO_BUILD_RUSTFLAGS','CARGO_BUILD_TARGET',
 'CREUSOT_RUSTC','CARGO_PATH','CREUSOT_CONTINUE','CARGO_TARGET_DIR',
 'CARGO_BUILD_RUSTC','CARGO_BUILD_RUSTDOC','CARGO_BUILD_RUSTC_WRAPPER','CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER'}
for name,value in os.environ.items():
    if value and (name in overrides or re.fullmatch(r'CARGO_TARGET_.+_RUSTFLAGS',name)):
        raise RuntimeError('Unpinned compiler/output override: '+name)
if os.environ.get('RUSTUP_TOOLCHAIN')!='nightly-2026-06-22':
    raise RuntimeError('Wrong extraction toolchain')

spec=importlib.util.spec_from_file_location('tools',ROOT/'scripts/check-tools.py');tools=importlib.util.module_from_spec(spec);spec.loader.exec_module(tools)
EXPECTED={
 'map_or_else2':{'vc_map_or_else2_Option_T':'product-body','vc_map_or_else_T':'standard-library-contract-abstraction'},
 'map_or_else2__refines':{'refines':'trait-refinement'},
 'option_model':{'vc_option_model_Option_T':'checked-identity-observation'},
}
def fingerprint():
    paths=[p for p in ROOT.rglob('*') if p.is_file() and not any(x in ('.work','target','verif','__pycache__') for x in p.relative_to(ROOT).parts)
       and p!=ROOT/'verification/results.md' and not p.is_relative_to(ROOT/'verification/evidence')]
    files={str(p.relative_to(ROOT)):tools.sha(p) for p in sorted(paths)}
    repo=ROOT.parents[2]
    for p in [repo/'scripts/aeneas_management/source.py',repo/'scripts/aeneas_management/__init__.py']:
        files[str(p.relative_to(repo))]=tools.sha(p)
    return {'files':files,'tools':tools.snapshot()}
def execute(cmd,name,env=None,cwd=ROOT):
    with (RUN/name).open('w') as f:
        subprocess.run(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
base=ROOT/'.work/runs';base.mkdir(parents=True,exist_ok=True)
RUN=Path(tempfile.mkdtemp(prefix='run-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-',dir=base))
print(RUN,flush=True)
execute(['python3.11','scripts/check-source.py'],'source-before.log')
execute(['python3.11','scripts/check-tools.py'],'tools-before.log')
before=fingerprint();(RUN/'inputs-before.json').write_text(json.dumps(before,indent=2,sort_keys=True)+'\n')
# Native observations use their own stable compiler and target directory.
native=dict(os.environ,RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(ROOT/'.work/native-target'))
execute(['cargo','test','--locked','--offline'],'native.log',native)
# A new Cargo output directory and new proof directory avoid generated/session reuse.
proof=dict(os.environ,CARGO_TARGET_DIR=str(RUN/'target'))
workspace=RUN/'workspace';workspace.mkdir()
for name in ('Cargo.toml','Cargo.lock','why3find.json'):
    shutil.copyfile(ROOT/name,workspace/name)
shutil.copytree(ROOT/'src',workspace/'src')
for p in workspace.rglob('*'):
    if p.is_file():assert tools.sha(p)==tools.sha(ROOT/p.relative_to(workspace))
execute(['cargo','creusot','--no-cache','--why3session','--','--locked','--offline'],'proof.log',proof,workspace)
files=sorted((workspace/'verif').rglob('*.coma'))
assert {p.stem for p in files}==set(EXPECTED), 'Unexpected generated scope'
roots=[]
for p in files:
    record=json.loads((p.with_suffix('')/'proof.json').read_text())
    named={name:tree for theory in record['proofs'].values() for name,tree in theory.items()}
    assert set(named)==set(EXPECTED[p.stem])
    session=ET.parse(p.with_suffix('')/'why3session.xml').getroot()
    goals={g.attrib['name']:g for g in session.iter('goal')}
    assert set(goals)==set(named)
    for name,tree in named.items():
        assert tree and tree.get('prover')=='z3', 'Missing/uncertified positive root'
        goal=goals[name];assert goal.attrib.get('proved')=='true'
        results=list(goal.iter('result'));assert results and all(x.attrib['status']=='valid' for x in results)
        roots.append({'name':name,'role':EXPECTED[p.stem][name],'generated':str(p.relative_to(RUN)),'prover':tree['prover'],'time':tree['time']})
assert len(roots)==4
for name in ('Cargo.toml','Cargo.lock','why3find.json'):
    assert tools.sha(workspace/name)==tools.sha(ROOT/name), 'Copied input changed during proof'
assert {p.relative_to(workspace/'src') for p in (workspace/'src').rglob('*') if p.is_file()} == {p.relative_to(ROOT/'src') for p in (ROOT/'src').rglob('*') if p.is_file()}
for p in (workspace/'src').rglob('*'):
    if p.is_file():assert tools.sha(p)==tools.sha(ROOT/p.relative_to(workspace)), 'Copied source changed during proof'
execute(['python3.11','scripts/check-source.py'],'source-after.log')
execute(['python3.11','scripts/check-tools.py'],'tools-after.log')
after=fingerprint();(RUN/'inputs-after.json').write_text(json.dumps(after,indent=2,sort_keys=True)+'\n');assert before==after,'Inputs changed during proof'
artifacts={str(p.relative_to(RUN)):tools.sha(p) for p in sorted(RUN.rglob('*')) if p.is_file() and 'target' not in p.relative_to(RUN).parts}
result={'schema_version':1,'status':'passed','scope':'Original delegated map_or_else2 partial correctness, trait refinement and checked observation; native tests and standard model stub separately classified.','host':'aarch64-apple-darwin','roots':roots,'native':{'branch_tests':3,'doctests':3},'before_after_equal':True,'files_sha256':artifacts}
(RUN/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print('PASSED: four positive valid roots; native checks separate; identical fingerprints.',flush=True)
