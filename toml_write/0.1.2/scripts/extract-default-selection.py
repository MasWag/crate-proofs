#!/usr/bin/env python3
"""Regenerate and compare the isolated, patched default-selection proof input."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
profile = root / 'aeneas/profiles/default'
config = json.loads((profile / 'extraction.json').read_text())
output = Path(os.environ['AENEAS_RUN_DIR']) / 'extraction-default-selection'
output.mkdir()
llbc = output / 'toml_write.llbc'
release = root / '.work/source'
patch = profile / 'patches/default-selection.patch'
maintained = (
    profile / 'proofs/Generated' / config['target'] / 'TomlDefaultModel/TomlWrite.lean'
)
extract_env = dict(os.environ, RUSTUP_TOOLCHAIN=os.environ['AENEAS_EXTRACT_RUST'])

methods = ['as_default', *(m for m in config['methods'] if m.startswith('as_'))]
selector_args = [
    argument for method in methods
    for argument in ('--start-from', f'crate::string::_::{method}',
                     '--include', f'crate::string::_::{method}')
]
include_args = [
    argument for name in ('DefaultEncoding' if t == 'Encoding' else t for t in config['types'])
    for argument in ('--include', f'crate::string::{name}')
]

# The root workspace may inherit Cargo patches. A separate staging directory also
# keeps the release inventory itself pristine.
with tempfile.TemporaryDirectory(prefix='toml-write-adapted-') as directory:
    stage = Path(directory)
    for name in ('Cargo.toml', 'Cargo.lock'):
        shutil.copyfile(root / name, stage / name)
    adapted = stage / '.work/source'
    shutil.copytree(release, adapted)
    adapted_string = adapted / 'src/string.rs'
    executable = stage / 'default-selection-check'
    extract_env['CARGO_TARGET_DIR'] = str(stage / 'target')
    native_env = dict(
        os.environ,
        TOML_WRITE_RELEASE_STRING=str(release / 'src/string.rs'),
        TOML_WRITE_ADAPTED_STRING=str(adapted_string),
    )
    commands = {
        'patch': ['patch', '-f', '-F', '0', '-i', str(patch), str(adapted_string)],
        'charon': ['charon', 'cargo', '--preset=aeneas', '--opaque', 'crate',
                   *selector_args, *include_args, '--dest-file', str(llbc),
                   '--', '--lib', '--locked'],
        'aeneas': ['aeneas', '-backend', 'lean', '-namespace', 'TomlDefault',
                   '-dest', str(output), str(llbc)],
        'native-build': ['rustc', '--edition=2021',
                         str(profile / 'default-selection-check.rs'), '-o', str(executable)],
        'native-compare': [str(executable)],
    }
    (output / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
    for name, argv in commands.items():
        env = native_env if name.startswith('native-') else extract_env
        with (output / f'{name}.log').open('wb') as log:
            subprocess.run(argv, cwd=stage, env=env, stdout=log, stderr=subprocess.STDOUT,
                           check=True)

    (output / 'source-sha256.json').write_text(json.dumps({
        label: hashlib.sha256(path.read_bytes()).hexdigest()
        for label, path in (
            ('release-src/string.rs', release / 'src/string.rs'),
            ('adapted-src/string.rs', adapted_string),
            ('default-selection.patch', patch),
        )
    }, indent=2) + '\n')

generated = output / 'TomlWrite.lean'
if {p.name for p in output.glob('*.lean')} != {generated.name}:
    raise ValueError('Unexpected adapted extraction output inventory')
body = generated.read_text()
if re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', body):
    raise ValueError('Incomplete adapted default-selection body')
for name in ('TomlStringBuilder', 'TomlKeyBuilder'):
    if not re.search(rf'(?m)^def string\.{name}\.as_default\b', body):
        raise ValueError(f'Missing adapted body {name}.as_default')
if generated.read_bytes() != maintained.read_bytes():
    raise ValueError('Regenerated adapted default-selection model differs')
print('Regenerated explicit-match defaults from the isolated Rust adaptation.')
print((output / 'native-compare.log').read_text().rstrip())
