#!/usr/bin/env python3
"""Run the pinned recorder's actual Creusot scanner on this annotated library."""
import json,os,re,shutil,subprocess,tempfile
from pathlib import Path
r=Path(__file__).resolve().parents[1]
store=Path(os.environ.get('CREUSOT_PROOFS_RS_STORE',r.parent/'.work/selected-tools')).resolve()
receipt=json.loads((store/'receipt.json').read_text())
assert receipt['inputs']['repositories']['proofs-rs']['revision']=='2446bcad7d492be2d2036629e5dc94d186a23213'
assert receipt['inputs']['repositories']['proofs-rs']['tree']=='b8eafed3b8232d5bee44fc7b8af0126937a99519'
cli=store/'proofs-rs/cli';probe=r/'.work/discovery-probe';(probe/'src').mkdir(parents=True,exist_ok=True)
shutil.copyfile(cli/'Cargo.toml',probe/'Cargo.toml');shutil.copyfile(cli/'Cargo.lock',probe/'Cargo.lock')
(probe/'Cargo.toml').write_text((probe/'Cargo.toml').read_text()+'\n[workspace]\n')
prefix=(cli/'src/main.rs').read_text().split('fn run() -> Result<()> {',1)[0]
prefix=re.sub(r'(?m)^mod (\w+);',lambda m:'#[path = '+json.dumps(str(cli/'src'/(m[1]+'.rs')))+']\nmod '+m[1]+';',prefix)
entry=r'''
fn main() -> Result<()> {
    let args = ProjectArgs { manifest_path: Some(PathBuf::from(MANIFEST)), ..Default::default() };
    let mut project = config::Project::load(&args)?;
    let config = project.config()?;
    project.cfg.insert(config.tool.name.clone());
    let contracts = scan::discover_for_tool(&project, &config.tool)?;
    anyhow::ensure!(contracts.len()==1,"Expected exactly one annotated product callable");
    anyhow::ensure!(contracts[0].api_paths == ["<core::option::Option<T> as option_ext::OptionExt<T>>::map_or_else2"],"Unexpected API");
    println!("{}",serde_json::to_string_pretty(&serde_json::json!({"api_paths":contracts[0].api_paths,"precondition":contracts[0].precondition,"first_line":contracts[0].first_line,"last_line":contracts[0].last_line}))?);
    Ok(())
}
'''.replace('MANIFEST',json.dumps(str(r/'Cargo.toml')))
(probe/'src/main.rs').write_text('#![allow(dead_code)]\n'+prefix+entry)
run=Path(tempfile.mkdtemp(prefix='discovery-',dir=r/'.work'))
env=dict(os.environ,RUSTUP_TOOLCHAIN='1.94.1')
with (run/'build.log').open('w') as err,(run/'result.json').open('w') as out:
    subprocess.run(['cargo','run','--release','--locked','--offline','--manifest-path',str(probe/'Cargo.toml')],cwd='/private/tmp',env=env,stdout=out,stderr=err,check=True)
observed=json.loads((run/'result.json').read_text())
assert 'None => default.precondition(())' in observed['precondition']
assert 'Some(t) => f.precondition((t,))' in observed['precondition']
print(run)
