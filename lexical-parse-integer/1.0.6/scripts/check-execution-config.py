#!/usr/bin/env python3
"""Check the inherited Cargo settings and the selected dependency cache."""
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
config = json.loads((ROOT / 'verification/execution-config.json').read_text())
if config['schema_version'] != 1:
    raise SystemExit('Unsupported execution-config schema')
if Path.cwd() != ROOT:
    raise SystemExit('Verification cwd changed')
if Path(os.environ['CARGO_HOME']).resolve() != (ROOT / config['cargo_home']).resolve():
    raise SystemExit('Version-local Cargo cache changed')
inherited = config['inherited_cargo_config']
path = Path(inherited['path'])
if not path.is_file():
    raise SystemExit(f'Missing pinned inherited Cargo config: {path}')
if hashlib.sha256(path.read_bytes()).hexdigest() != inherited['sha256']:
    raise SystemExit('Inherited Cargo config changed')
print('Pinned inherited Cargo config and version-local Cargo cache checked')
