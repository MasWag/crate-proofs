#!/usr/bin/env python3
"""Regenerate the unchanged Rust bodies and inventory their two stdlib boundaries."""

import json
import os
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
profile = root / 'aeneas/profiles/default'
config = json.loads((profile / 'extraction.json').read_text())
output = Path(os.environ['AENEAS_RUN_DIR']) / 'extraction-split'
output.mkdir()
llbc = output / 'toml_write.llbc'
env = dict(os.environ, RUSTUP_TOOLCHAIN=os.environ['AENEAS_EXTRACT_RUST'])
rust_version = subprocess.check_output(['rustc', '-vV'], cwd=root, env=env, text=True)
if f"host: {config['target']}" not in rust_version.splitlines():
    raise ValueError('Split extraction target does not match the pinned Rust host')

selector_args = [
    argument for method in config['methods']
    for argument in ('--start-from', f'crate::string::_::{method}',
                     '--include', f'crate::string::_::{method}')
]
include_args = [
    argument for name in config['types']
    for argument in ('--include', f'crate::string::{name}')
]
commands = {
    'charon': ['charon', 'cargo', '--preset=aeneas', '--opaque', 'crate',
               *selector_args, *include_args, '--dest-file', str(llbc),
               '--', '--lib', '--locked'],
    'aeneas': ['aeneas', '-backend', 'lean', '-split-files', '-dest', str(output), str(llbc)],
}
(output / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
for name, argv in commands.items():
    with (output / f'{name}.log').open('wb') as log:
        subprocess.run(argv, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True)

model_dir = profile / 'proofs/Generated' / config['target'] / 'TomlWrite'
template = 'FunsExternal_Template.lean'
expected = {*config['models'], template}
if {p.name for p in output.glob('*.lean')} != expected:
    raise ValueError('Unexpected split extraction output inventory')
for name, required in config['models'].items():
    generated = output / name
    body = generated.read_text()
    if re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', body):
        raise ValueError(f'Incomplete generated body in {name}')
    for definition in required:
        if not re.search(rf'(?m)^\s*(?:def|structure|inductive)\s+{re.escape(definition)}\b', body):
            raise ValueError(f'Missing {definition} in {name}')
    if generated.read_bytes() != (model_dir / name).read_bytes():
        raise ValueError(f'Regenerated model differs: {name}')

template_body = (output / template).read_text()
external_declarations = re.findall(
    r'(?m)^[ \t]*(?:[A-Za-z]+[ \t]+)*(?:axiom|opaque|partial[ \t]+def)\b[^\n]*',
    template_body,
)
if external_declarations != [
    'axiom core.str.Str.is_empty : Str → Result Bool',
    'axiom core.str.Str.as_bytes : Str → Result (Slice Std.U8)',
]:
    raise ValueError('Unexpected external standard-library boundaries')
print('Regenerated unchanged Rust bodies; FunsExternal models two named str observations.')
