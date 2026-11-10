#!/usr/bin/env python3.11
"""Extract exact release facade, then reproduce unsupported float-field Lean emission."""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parents[1]
work = Path(tempfile.mkdtemp(prefix='original-facade-', dir=ROOT / '.work'))
out = work / 'generated'
subprocess.run([sys.executable, str(ROOT.parents[1] / 'scripts/aeneas-extract.py'), str(ROOT), '--config', str(ROOT / 'verification/original-facade-extraction.json'), '--output', str(out)], check=True)
# Use the pinned prepared Lake environment, without modifying generated Lean.
lean = ROOT / '.work/build/default/aarch64-apple-darwin/proofs'
proc = subprocess.run(['lake', 'env', 'lean', str(out / 'Facade.lean')], cwd=lean, capture_output=True, text=True)
(work / 'lean.log').write_text(proc.stdout + proc.stderr)
if proc.returncode == 0:
    raise SystemExit('Original facade now builds; update adapted profile and coverage')
for text in ['Failed to infer universe levels', 'as_f64', 'as_f32']:
    if text not in proc.stdout + proc.stderr:
        raise SystemExit(f'Original facade failed at changed boundary: {work}')
print(f'Unchanged release facade extraction succeeds, but generated unused AsPrimitive float fields do not compile. No generated edits; evidence: {work}')
