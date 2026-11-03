#!/usr/bin/env python3
"""Finite comparison; this is not a proof of release equivalence."""
from pathlib import Path
import shutil
import subprocess

profile = Path(__file__).resolve().parents[1]
root = profile.parents[2]
source = root / '.work/experimental-compare.rs'
binary = root / '.work/experimental-compare'
shutil.copyfile(profile / 'scripts/compare.rs', source)
subprocess.run(['rustc', '--edition=2021', '-O', str(source), '-o', str(binary)], check=True)
subprocess.run([str(binary)], check=True)
