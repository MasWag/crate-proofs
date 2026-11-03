#!/usr/bin/env python3
"""Exercise the pinned CLI adapter's real discovery without recording or publication."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    sys.path.insert(0, str(root.parents[1] / 'scripts'))
    from aeneas_management import tools
    profile = root / 'aeneas/profiles/default'
    lock = json.loads((profile / 'toolchain.lock.json').read_text())
    store = (root / '.work/selected-tools').resolve()
    tools.check(store, lock)
    cli = store / 'proofs-rs/cli'
    probe = root / '.work/api-discovery-probe'
    (probe / 'src').mkdir(parents=True, exist_ok=True)
    shutil.copyfile(cli / 'Cargo.toml', probe / 'Cargo.toml')
    shutil.copyfile(cli / 'Cargo.lock', probe / 'Cargo.lock')
    manifest = probe / 'Cargo.toml'
    manifest.write_text(manifest.read_text() + '\n[workspace]\n')
    # Import the actual pinned modules; only the entrypoint below is custom.
    prefix = (cli / 'src/main.rs').read_text().split('fn run() -> Result<()> {', 1)[0]
    prefix = re.sub(r'(?m)^mod (\w+);', lambda m: '#[path = ' + json.dumps(str(cli / 'src' / (m[1] + '.rs'))) + ']\nmod ' + m[1] + ';', prefix)
    entrypoint = r'''
fn main() -> Result<()> {
    let args = ProjectArgs {
        manifest_path: Some(PathBuf::from(MANIFEST)),
        proofs_config: Some(PathBuf::from("aeneas/profiles/default/proofs.toml")),
        ..Default::default()
    };
    let project = config::Project::load(&args)?;
    let config = project.config()?;
    let contracts = scan::discover_for_tool(&project, &config.tool)?;
    anyhow::ensure!(contracts.len() == 5, "expected five actual public callables");
    for (proof, contract) in config.tool.proofs.iter().zip(&contracts) {
        anyhow::ensure!(contract.api_paths.contains(&proof.api), "API mapping mismatch");
    }
    let output = serde_json::json!({"package":project.name,"version":project.version,
        "discovered":contracts.iter().map(|c| serde_json::json!({"api_paths":c.api_paths,"precondition":c.precondition})).collect::<Vec<_>>()});
    println!("{}", serde_json::to_string_pretty(&output)?);
    Ok(())
}
'''.replace('MANIFEST', json.dumps(str(root / 'Cargo.toml')))
    (probe / 'src/main.rs').write_text('#![allow(dead_code)]\n' + prefix + entrypoint)
    assert sha(probe / 'Cargo.lock') == sha(cli / 'Cargo.lock')
    runs = root / '.work/api-discovery-runs'
    runs.mkdir(exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='discovery-', dir=runs))
    for source in ['Cargo.toml', 'Cargo.lock', 'src/main.rs']:
        target = run / source
        target.parent.mkdir(exist_ok=True)
        shutil.copyfile(probe / source, target)
    env = dict(os.environ, RUSTUP_TOOLCHAIN=lock['native_rust'])
    command = ['cargo', 'run', '--release', '--locked', '--manifest-path', str(manifest)]
    if args.offline:
        command.append('--offline')
    with (run / 'build.log').open('w') as log, (run / 'stdout.json').open('w') as output:
        subprocess.run(command, cwd=root, env=env, stdout=output, stderr=log, check=True)
    observed = json.loads((run / 'stdout.json').read_text())
    report = tomllib.loads((profile / 'proofs.toml').read_text())
    mappings = report['tool']['proofs']
    assert len(observed['discovered']) == len(mappings) == 5
    for actual, expected in zip(observed['discovered'], mappings):
        assert expected['api'] in actual['api_paths']
        assert actual['precondition'] == expected['precondition'] == 'true'
    tools.check(store, lock)
    result = dict(observed, schema_version=1, status='passed', scope='Actual pinned CLI callable discovery; not recording or publication.',
                  proofs_rs_revision=lock['repositories']['proofs-rs']['revision'],
                  proofs_rs_tree=lock['repositories']['proofs-rs']['tree'],
                  cli_lock_sha256=sha(cli / 'Cargo.lock'), probe_source_sha256=sha(probe / 'src/main.rs'),
                  tool_lock_sha256=sha(profile / 'toolchain.lock.json'),
                  probe_binary_sha256=sha(probe / 'target/release/cargo-proofs'))
    (run / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(run)


if __name__ == '__main__':
    main()
