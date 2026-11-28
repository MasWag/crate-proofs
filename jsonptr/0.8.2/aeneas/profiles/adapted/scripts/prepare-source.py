#!/usr/bin/env python3
"""Derive .work/adapted from the locked release plus the recorded patches.

The release tree in .work/source is never modified. A fresh copy is patched in a
temporary directory and every resulting file is compared byte for byte with the
SHA-256 inventory in adapted-source.json. Without --check the verified tree
replaces .work/adapted; with --check the existing .work/adapted must equal it.
This establishes patch identity only, not equivalence to the release bodies.
"""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

profile = Path(__file__).resolve().parents[1]
root = profile.parents[2]
release = root / '.work/source'
destination = root / '.work/adapted'
patches = ['cargo-workspace.patch', 'adapted-bodies.patch', 'adapted-api.patch']


def inventory(tree):
    return {p.relative_to(tree).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(tree.rglob('*')) if p.is_file()}


def main():
    expected = json.loads((profile / 'adapted-source.json').read_text())
    if expected['patches'] != {name: hashlib.sha256((profile / 'patches' / name).read_bytes()).hexdigest()
                               for name in patches}:
        raise ValueError('Recorded patch digests differ from adapted-source.json')
    with tempfile.TemporaryDirectory(dir=root / '.work') as temporary:
        trial = Path(temporary) / 'adapted'
        shutil.copytree(release, trial, symlinks=False)
        for name in patches:
            subprocess.run(['patch', '--batch', '--forward', '-p1', '-i', str(profile / 'patches' / name)],
                           cwd=trial, check=True, stdout=subprocess.DEVNULL)
        leftovers = [p for p in trial.rglob('*') if p.suffix in ('.orig', '.rej')
                     and p.relative_to(trial).as_posix() not in expected['files']]
        if leftovers:
            raise ValueError(f'Patch left backup or reject files: {leftovers}')
        actual = inventory(trial)
        if actual != expected['files']:
            changed = sorted(set(actual.items()) ^ set(expected['files'].items()))
            raise ValueError(f'Adapted source differs from the recorded inventory: {changed[:6]}')
        if '--check' in sys.argv:
            if inventory(destination) != actual:
                raise ValueError(f'Adapted source drift in {destination}')
        else:
            if destination.exists():
                shutil.rmtree(destination)
            shutil.copytree(trial, destination)
    print('Adapted source equals the locked release plus the recorded patches (not formal equivalence).')


if __name__ == '__main__':
    main()
