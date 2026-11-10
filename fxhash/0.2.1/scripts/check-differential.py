#!/usr/bin/env python3
"""Run finite release-versus-adapted Hasher traces outside ancestor Cargo config."""
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
manifest = root / 'verification/differential/Cargo.toml'
target = root / '.work/build/differential'
for mode in ('debug', 'release'):
    command = ['cargo', 'test', '--locked', '--offline', '--manifest-path', str(manifest),
               '--target-dir', str(target)]
    if mode == 'release':
        command.append('--release')
    print('Running', mode, flush=True)
    subprocess.run(command, cwd=tempfile.gettempdir(), check=True)
