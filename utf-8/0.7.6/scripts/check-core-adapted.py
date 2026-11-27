#!/usr/bin/env python3
"""Reconstruct/check exact derived inputs, without changing the release tree."""
import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root.parents[1] / 'scripts'))
from aeneas_management import source

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true')
parser.add_argument('--destination', type=Path, default=root / '.work/core-adapted-source')
args = parser.parse_args()
dest = args.destination.absolute()
profile = root / 'aeneas/profiles/core_adapted'
if dest.is_symlink() or any(p.is_symlink() for p in dest.parents):
    raise ValueError(f'Symlink in adapted input path: {dest}')
if dest.exists() and not dest.is_dir():
    raise ValueError(f'Adapted input path is not a directory: {dest}')


def inventory(directory):
    if directory.is_symlink() or any(p.is_symlink() for p in directory.parents):
        raise ValueError(f'Symlink in adapted input path: {directory}')
    files = source.inventory(directory)
    directories = {p.relative_to(directory).as_posix() for p in directory.rglob('*') if p.is_dir()}
    return files, directories


with tempfile.TemporaryDirectory(dir=root / '.work') as tmp:
    trial = Path(tmp) / 'source'
    subprocess.run([sys.executable, str(root / 'scripts/prepare-core-adapted.py'), str(trial)],
                   check=True, stdout=subprocess.DEVNULL)
    shutil.copy2(profile / 'Cargo.lock', trial / 'Cargo.lock')
    expected, expected_dirs = inventory(trial)
    if dest.exists() or dest.is_symlink():
        actual, actual_dirs = inventory(dest)
        extra = sorted(set(actual) - set(expected))
        extra_dirs = sorted(actual_dirs - expected_dirs)
        if extra or extra_dirs:
            raise ValueError(f'Unexpected adapted inputs: files={extra}, directories={extra_dirs}')
    elif args.check:
        raise ValueError(f'Adapted input directory missing: {dest}')
    if args.check:
        if actual != expected or actual_dirs != expected_dirs:
            raise ValueError('Adapted input inventory/content/mode drift')
    else:
        dest.mkdir(parents=True, exist_ok=True)
        for name in expected:
            target = dest / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(trial / name, target)
        if inventory(dest) != (expected, expected_dirs):
            raise ValueError('Adapted input reconstruction did not produce the exact inventory')
print('Exact adapted input inventory matches explicit patch; release equivalence remains a reviewed argument.')
