#!/usr/bin/env python3
"""Reproduce unsupported release-body boundaries; never install models from probes."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
sys.path.insert(0, str(REPO / 'scripts'))
from aeneas_management import tools

profile = ROOT / 'aeneas/profiles/default'
lock, key = tools.identity(profile)
store = REPO / '.work/tools' / key
tools.check(store, lock)
env = tools.environment(store, lock)
env.update(RUSTUP_TOOLCHAIN=lock['extraction_rust'], CARGO_NET_OFFLINE='true',
           CARGO_TARGET_DIR=str(ROOT / '.work/build/boundary-probes'))
parent = ROOT / '.work/boundary-probes'
parent.mkdir(parents=True, exist_ok=True)
run = Path(tempfile.mkdtemp(prefix='run-', dir=parent))
probes = {
    'decode': ('crate::decode', []),
    'decode-std': ('crate::decode', ['core::str::converts::from_utf8', 'core::str::converts::from_utf8_unchecked', 'core::str::validations::run_utf8_validation', 'core::str::validations::utf8_char_width', 'core::str::error::Utf8Error', 'core::str::error::_::valid_up_to', 'core::str::error::_::error_len']),
    'offsets-std': ('crate::Incomplete::try_complete_offsets', ['core::str::converts::from_utf8', 'core::str::converts::from_utf8_unchecked', 'core::str::validations::run_utf8_validation', 'core::str::validations::utf8_char_width', 'core::str::error::Utf8Error', 'core::str::error::_::valid_up_to', 'core::str::error::_::error_len']),
    'try_complete': ('crate::Incomplete::try_complete', []),
    'feed': ('crate::lossy::LossyDecoder::feed', []),
    'read': ('crate::read::BufReadDecoder::next_strict', []),
}
results = {}
for name, (entry, includes) in probes.items():
    cfg = run / (name + '.json')
    cfg.write_text(json.dumps({'entries': [entry], 'llbc': 'Utf8.llbc',
        'cargo_args': ['--lib', '--locked', '--offline'], 'charon_include': includes,
        'models': {'Utf8.lean': [entry.removeprefix('crate::').replace('::', '.')]}}, indent=2) + '\n')
    command = [sys.executable, str(REPO / 'scripts/aeneas-extract.py'), str(ROOT),
               '--config', str(cfg), '--output', str(run / name)]
    with (run / (name + '-driver.log')).open('w') as log:
        completed = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
    results[name] = {'command': command, 'exit_code': completed.returncode}
(run / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
print(run)
print('Diagnostic output only: failed/partial translations are excluded from maintained proofs.')
