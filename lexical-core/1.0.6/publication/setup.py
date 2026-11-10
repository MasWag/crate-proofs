#!/usr/bin/env python3.11
"""Prepare upstream provenance and optional checked Git Lake dependency caches.

This prepares no proof result. cargo-proofs independently runs standard Lake and
its named-theorem axiom audits. The selected Rust library remains the explicit
trait-bound-erased verification fork, not the restored upstream source.
"""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parent
WORK = ROOT / '.work'
WORK.mkdir(exist_ok=True)
lock = json.loads((ROOT / 'upstream-source.lock.json').read_text())
assert lock['kind'] == 'registry' and lock['name'] == 'lexical-core' and lock['version'] == '1.0.6'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
cache = WORK / 'cache'
cache.mkdir(exist_ok=True)
archive = cache / (lock['sha256'] + '.crate')
if not archive.exists():
    donor = ROOT.parent / '.work/cache' / archive.name
    if donor.is_file():
        shutil.copyfile(donor, archive)
    else:
        assert lock['url'].startswith('https://static.crates.io/crates/lexical-core/')
        request = urllib.request.Request(lock['url'], headers={'User-Agent': 'lexical-core-publication-provenance/1'})
        with urllib.request.urlopen(request, timeout=60) as response, archive.open('wb') as out:
            shutil.copyfileobj(response, out)
assert sha(archive) == lock['sha256'], 'Upstream archive checksum changed'

def inventory(root):
    found = {}
    for p in root.rglob('*'):
        assert not p.is_symlink(), 'Unexpected upstream symlink'
        if p.is_file():
            found[p.relative_to(root).as_posix()] = {'sha256': sha(p), 'executable': bool(p.stat().st_mode & 0o111)}
    return found

source = WORK / 'upstream-source'
if not source.exists():
    stage = Path(tempfile.mkdtemp(prefix='upstream-', dir=WORK))
    with tarfile.open(archive, 'r:gz') as tar:
        for member in tar:
            if member.isdir():
                continue
            path = PurePosixPath(member.name)
            assert member.isfile() and path.parts[0] == 'lexical-core-1.0.6' and '..' not in path.parts
            destination = stage.joinpath(*path.parts[1:])
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(tar.extractfile(member).read())
            destination.chmod(member.mode & 0o777)
    assert inventory(stage) == lock['files'], 'Restored upstream inventory changed'
    stage.rename(source)
assert inventory(source) == lock['files'], 'Prepared upstream inventory changed'
print('Verified checksum-pinned upstream archive/full inventory as correspondence provenance; selected library is the documented fork.')
subprocess.run([os.environ.get('PYTHON', 'python3.11'), str(ROOT / 'check-source.py')], check=True)

# Optional performance input. Every source revision, origin and clean tracked
# tree is checked before normal Lake is allowed to reuse its compiled artifacts.
donor = os.environ.get('LEXICAL_CORE_PUBLICATION_LAKE_CACHE')
if donor:
    donor = Path(donor).resolve()
    manifest = json.loads((ROOT / 'proofs/lake-manifest.json').read_text())
    packages = ROOT / 'proofs/.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    for item in manifest['packages']:
        assert item['type'] == 'git'
        candidate = (donor / item['name']).resolve()
        assert candidate.is_dir(), f'Missing donor: {item["name"]}'
        def git(*args):
            return subprocess.check_output(['git', '-C', str(candidate), *args], text=True).strip()
        assert git('rev-parse', 'HEAD') == item['rev'], f'Donor revision mismatch: {item["name"]}'
        assert not git('status', '--porcelain', '--untracked-files=no'), f'Dirty donor source: {item["name"]}'
        assert git('remote', 'get-url', 'origin') == item['url'], f'Donor origin mismatch: {item["name"]}'
        destination = packages / item['name']
        if destination.is_symlink():
            assert destination.resolve() == candidate, f'Different existing dependency symlink: {item["name"]}'
        elif destination.exists():
            assert subprocess.check_output(['git', '-C', str(destination), 'rev-parse', 'HEAD'], text=True).strip() == item['rev']
            assert not subprocess.check_output(['git', '-C', str(destination), 'status', '--porcelain', '--untracked-files=no'], text=True).strip()
            assert subprocess.check_output(['git', '-C', str(destination), 'remote', 'get-url', 'origin'], text=True).strip() == item['url']
        else:
            destination.symlink_to(candidate, target_is_directory=True)
    print('Seeded only revision/origin/clean-source-checked Git Lake dependency caches; standard Lake/audits still required.')
