#!/usr/bin/env python3.11
"""Check pinned registry archives and every restored dependency file, offline."""
import argparse
import hashlib
from pathlib import Path
import tarfile
import tomllib
ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--lock', default='Cargo.lock')
args = parser.parse_args()
packages = tomllib.loads((ROOT / args.lock).read_text())['package']
registry = ROOT / '.work/cargo-home/registry'
count = 0
for package in packages:
    if not package.get('source', '').startswith('registry+'):
        continue
    stem = f"{package['name']}-{package['version']}"
    archives = list((registry / 'cache').glob(f'*/{stem}.crate'))
    sources = list((registry / 'src').glob(f'*/{stem}'))
    assert len(archives) == len(sources) == 1, f'Missing/ambiguous cached dependency: {stem}'
    archive, source = archives[0], sources[0]
    assert hashlib.sha256(archive.read_bytes()).hexdigest() == package['checksum'], f'Archive changed: {stem}'
    expected = {}
    with tarfile.open(archive, 'r:gz') as tar:
        for member in tar:
            if member.isdir():
                continue
            assert member.isfile(), f'Unexpected archive member: {member.name}'
            relative = Path(member.name).relative_to(stem).as_posix()
            assert '..' not in Path(relative).parts
            expected[relative] = hashlib.sha256(tar.extractfile(member).read()).hexdigest()
    actual = {}
    for path in source.rglob('*'):
        assert not path.is_symlink(), f'Unexpected registry symlink: {path}'
        if path.is_file():
            relative = path.relative_to(source).as_posix()
            if relative in {'.cargo-ok', '.cargo-checksum.json'}:
                continue
            actual[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    assert actual == expected, f'Restored dependency source differs from archive: {stem}'
    count += 1
print(f'Checked {count} checksum-pinned registry archives and full restored file inventories from {args.lock}.')
