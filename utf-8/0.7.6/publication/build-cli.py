#!/usr/bin/env python3
"""Build/test the explicitly patched publication CLI; never modify verifier tools."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root.parents[1] / 'scripts'))
from aeneas_management import tools

spec = json.loads((root / 'publication/cli.lock.json').read_text())
lock, key = tools.identity(root / 'aeneas/profiles/default')
store = root.parents[1] / '.work/tools' / key
tools.check(store, lock)
source = store / 'proofs-rs'
if tools.git(source, 'rev-parse', 'HEAD') != spec['base_revision']:
    raise ValueError('Publication CLI base differs from its lock')
for field in ('base_preparation_patch', 'publication_patch'):
    entry = spec[field]
    if hashlib.sha256((root / entry['path']).read_bytes()).hexdigest() != entry['sha256']:
        raise ValueError(f'Publication patch checksum mismatch: {field}')
if hashlib.sha256((source / 'cli/Cargo.lock').read_bytes()).hexdigest() != spec['cargo_lock_sha256']:
    raise ValueError('Publication CLI dependency lock differs')
parent = root / '.work/publication-cli'
parent.mkdir(parents=True, exist_ok=True)
run = Path(tempfile.mkdtemp(prefix='run-', dir=parent))
shutil.copytree(source / 'cli', run / 'cli', ignore=shutil.ignore_patterns('target'))
with (run / 'patch.log').open('w') as log:
    subprocess.run(['patch', '--batch', '-p1', '-i', str(root / spec['publication_patch']['path'])],
                   cwd=run, stdout=log, stderr=subprocess.STDOUT, check=True)
env = os.environ.copy()
env.update(RUSTUP_TOOLCHAIN=spec['native_rust'], CARGO_TARGET_DIR=str(parent / 'target'))
commands = []
# Cargo searches configuration from its execution directory. This disposable
# directory excludes repository ancestor .cargo settings without changing homes.
with tempfile.TemporaryDirectory(prefix='utf8-cli-cargo-') as cwd:
    for group in ['scan::tests', 'config::tests', 'draft::tests', None]:
        args = ['cargo', 'test' if group else 'build', '--release', '--locked', '--offline',
                '--manifest-path', str(run / 'cli/Cargo.toml')]
        if group:
            args += ['--bin', 'cargo-proofs', group]
        name = (group or 'build').replace('::', '-')
        with (run / (name + '.log')).open('w') as log:
            subprocess.run(args, cwd=cwd, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        commands.append(args)
binary = parent / 'target/release/cargo-proofs'
receipt = {'status': 'built-and-tested', 'scope': 'utf-8 0.7.6 publication compatibility only',
           'cli_lock_sha256': hashlib.sha256((root / 'publication/cli.lock.json').read_bytes()).hexdigest(),
           'binary': str(binary), 'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
           'commands': commands, 'verifier_tools_unchanged': True}
(run / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(binary)
print(run / 'receipt.json')
