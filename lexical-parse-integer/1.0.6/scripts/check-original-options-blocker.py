#!/usr/bin/env python3.11
"""Retain fresh diagnostics for the unchanged release options blocker."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
CONFIG = ROOT / 'verification/original-options-extraction.json'
work = Path(tempfile.mkdtemp(prefix='original-options-', dir=ROOT / '.work'))
output = work / 'output'
env = os.environ.copy()
env['RUSTUP_TOOLCHAIN'] = env['AENEAS_EXTRACT_RUST']
proc = subprocess.run(
    [sys.executable, str(REPO / 'scripts/aeneas-extract.py'), str(ROOT),
     '--config', str(CONFIG), '--output', str(output)],
    capture_output=True, text=True, env=env)
charon = (output / 'charon.log').read_text() if (output / 'charon.log').exists() else ''
aeneas = (output / 'aeneas.log').read_text() if (output / 'aeneas.log').exists() else ''
clean = re.sub(r'\x1b\[[0-9;?]*[ -/]*[@-~]', '', aeneas)
if proc.returncode == 0:
    raise SystemExit('Original options blocker now extracts; update proof coverage')
if 'Finished `dev` profile' not in charon:
    raise SystemExit('Original options probe did not reach Aeneas: ' + proc.stderr[-1000:])
if 'Internal error, please file an issue' not in clean or 'OptionsBuilder}::build_strict' not in clean:
    raise SystemExit('Original options failed at a changed boundary: ' + clean[-1000:])
if "options.rs', lines 146:15-146:20" not in clean:
    raise SystemExit('Expected release options source span not reported')
print(f'Original build_strict and dependent constants remain blocked at Aeneas interp/Interp.ml:629; logs: {output}')
