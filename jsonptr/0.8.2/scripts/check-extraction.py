#!/usr/bin/env python3
"""Regenerate the jsonptr model with the release bodies and pinned tool binaries."""
import json
import os
from pathlib import Path
import re
import subprocess


def main():
    root = Path(__file__).resolve().parent.parent
    profile = root / 'aeneas/profiles/default'
    config = json.loads((profile / 'extraction.json').read_text())
    lock = json.loads((profile / 'toolchain.lock.json').read_text())
    output = Path(os.environ['AENEAS_RUN_DIR']) / 'generated'
    output.mkdir()
    llbc = output / config['llbc']
    env = dict(os.environ, RUSTUP_TOOLCHAIN=lock['extraction_rust'])
    commands = [
        ('charon', [
            'charon', 'cargo', '--preset=aeneas', '--sysroot=default', '--mir=optimized',
            '--rustc-arg=-Zmir-strip-debuginfo=all-locals', '--opaque', 'crate',
            '--remove-unused-clauses',
            *[arg for entry in config['entries'] for arg in ('--start-from', entry)],
            *[arg for entry in config['local_scope']['include'] for arg in ('--include', entry)],
            '--dest-file', str(llbc), '--', *config['cargo_args'],
        ]),
        ('aeneas', ['aeneas', '-backend', 'lean', '-dest', str(output), str(llbc)]),
    ]
    for name, command in commands:
        with (output / f'{name}.log').open('w') as log:
            print(command, file=log, flush=True)
            subprocess.run(command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    actual = {path.relative_to(output).as_posix() for path in output.rglob('*.lean')}
    expected = set(config['models'])
    if actual != expected:
        raise ValueError(f'Generated files {actual} differ from maintained inventory {expected}')
    for name in sorted(actual):
        model = (output / name).read_bytes()
        source = model.decode('utf-8')
        if re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', source):
            raise ValueError(f'Generated model contains an unchecked declaration: {name}')
        for definition in config['models'][name]:
            if not re.search(rf'(?m)^\s*def\s+{re.escape(definition)}(?=\s|\(|:)', source):
                raise ValueError(f'Generated model is missing {definition} in {name}')
        maintained = profile / 'proofs/Generated/aarch64-apple-darwin' / name
        if model != maintained.read_bytes():
            raise ValueError(f'Generated model differs from maintained {name}')


if __name__ == '__main__':
    main()
