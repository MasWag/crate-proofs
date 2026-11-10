#!/usr/bin/env python3
"""Reproduce the first unsupported boundary on the unchanged parser body."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
EXTRACT = REPO / 'scripts/aeneas-extract.py'
CONFIG = ROOT / 'verification/original-parser-extraction.json'

work = Path(tempfile.mkdtemp(prefix='original-parser-', dir=ROOT / '.work'))
output = work / 'output'
env = os.environ.copy()
env['RUSTUP_TOOLCHAIN'] = env['AENEAS_EXTRACT_RUST']
proc = subprocess.run(
    [sys.executable, str(EXTRACT), str(ROOT), '--config', str(CONFIG),
     '--output', str(output)], capture_output=True, text=True, env=env)
if proc.returncode == 0:
    raise SystemExit('Original parser now extracts; update scope and proof coverage')
charon_log = (output / 'charon.log').read_text() if (output / 'charon.log').exists() else ''
aeneas_log = (output / 'aeneas.log').read_text() if (output / 'aeneas.log').exists() else ''
clean = re.sub(r'\x1b\[[0-9;?]*[ -/]*[@-~]', '', aeneas_log)
if 'Finished `dev` profile' not in charon_log:
    raise SystemExit('Original parser did not reach Aeneas: ' + proc.stderr[-1000:])
if 'Breaks to outer loops are not supported yet' not in clean:
    raise SystemExit('Original parser failed at a changed boundary: ' + clean[-1000:])
if "algorithm::algorithm_complete" not in clean:
    raise SystemExit('Expected original algorithm body not identified')
print(f'Original algorithm_complete blocked at Aeneas outer-loop break after Charon success; logs: {output}')
