#!/usr/bin/env python3.11
"""Reproduce actual dependency-body boundaries without modifying verifier tools."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parents[1]
EXTRACT = ROOT.parents[1] / 'scripts/aeneas-extract.py'
EXPECTED = {
    'parse_u32': ['Early returns inside of loops are not supported yet', 'algorithm::algorithm_complete'],
    'parse_partial_u32': ['Early returns inside of loops are not supported yet', 'algorithm::algorithm_partial'],
    'parse_partial_f64': ['Breaks to outer loops are not supported yet', 'slow::parse_mantissa'],
    'parse_f64': ['Breaks to outer loops are not supported yet', 'slow::parse_mantissa'],
    'write_u32': ['Unreachable', "lexical-util-1.0.7/src/num.rs', lines 151:12-151:34"],
    'write_f64': ['Internal error, please file an issue', 'write::write_special'],
}
work = Path(tempfile.mkdtemp(prefix='core-boundaries-', dir=ROOT / '.work'))
summary = {}
for name, messages in EXPECTED.items():
    output = work / name
    proc = subprocess.run([sys.executable, str(EXTRACT), str(ROOT), '--config', str(ROOT / 'verification' / ('probe-' + name + '-selected.json')), '--output', str(output)], capture_output=True, text=True)
    charon = (output / 'charon.log').read_text() if (output / 'charon.log').exists() else ''
    aeneas = (output / 'aeneas.log').read_text() if (output / 'aeneas.log').exists() else ''
    clean = re.sub(r'\x1b\[[0-9;?]*[ -/]*[@-~]', '', aeneas)
    if proc.returncode == 0 or 'Finished `dev` profile' not in charon or not all(m in clean for m in messages):
        raise SystemExit(f'{name}: expected boundary changed; inspect {output}: {proc.stderr[-800:]}')
    summary[name] = {'boundary': messages, 'charon_succeeded': True, 'aeneas_succeeded': False, 'log_sha256': hashlib.sha256(aeneas.encode()).hexdigest()}
(work / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(f'All six concrete default-feature release parse/partial/write call graphs reached Charon success and expected Aeneas boundaries. No algorithm acceptance. Evidence: {work}')
