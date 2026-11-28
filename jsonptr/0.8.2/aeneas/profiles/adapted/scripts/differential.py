#!/usr/bin/env python3
"""Run the native release-vs-adapted differential comparison in debug and release.

Finite evidence for the release-correspondence obligations; not a proof.
Requires .work/adapted (prepared by prepare-source.py).
"""
from pathlib import Path
import subprocess
import sys

profile = Path(__file__).resolve().parents[1]
for harness in (profile / 'differential', profile / 'differential-api'):
  for extra in ([], ['--release']):
    result = subprocess.run(['cargo', 'run', '--locked', '--offline', *extra], cwd=harness,
                            capture_output=True, text=True)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    if result.returncode != 0 or 'all compared results agree' not in result.stdout:
        raise SystemExit(f'differential comparison failed ({extra or ["debug"]})')
