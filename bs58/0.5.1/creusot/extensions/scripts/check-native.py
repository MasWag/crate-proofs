#!/usr/bin/env python3
"""Fingerprint and compare extension APIs against the exact registry release."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import tomllib

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain', default='1.94.1')
parser.add_argument('--cargo-home')
parser.add_argument('--rustup-home')
args = parser.parse_args()
ext = Path(__file__).resolve().parent.parent
root = ext.parent
parent = root / '.work/extensions'
parent.mkdir(parents=True, exist_ok=True)
run = Path(tempfile.mkdtemp(prefix='native-', dir=parent))
(run / 'tmp').mkdir()
env = os.environ.copy()
for name, value in [('CARGO_HOME', args.cargo_home), ('RUSTUP_HOME', args.rustup_home)]:
    if value:
        env[name] = str(Path(value).resolve())
env.update(CARGO_TARGET_DIR=str(run / 'target'), TMPDIR=str(run / 'tmp'), CARGO_NET_OFFLINE='true')
manifest = ext / 'native/Cargo.toml'
cargo = shutil.which('cargo')
base = [cargo, '+' + args.toolchain]
metadata = json.loads(subprocess.check_output(base + [
    'metadata', '--locked', '--offline', '--format-version', '1',
    '--manifest-path', str(manifest)], env=env, text=True))
release = next(p for p in metadata['packages'] if p['name'] == 'bs58' and p['version'] == '0.5.1')
release_dir = Path(release['manifest_path']).parent
source_lock = json.loads((root / '../source.lock.json').read_text())
lock = tomllib.loads(manifest.with_name('Cargo.lock').read_text())
entry = next(p for p in lock['package'] if p['name'] == 'bs58' and p['version'] == '0.5.1')
assert entry['checksum'] == source_lock['sha256']


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_release():
    for name, expected in source_lock['files'].items():
        assert digest(release_dir / name) == expected['sha256'], name


paths = [Path(__file__), root / '../source.lock.json', ext / 'crate/Cargo.toml',
         ext / 'crate/Cargo.lock', manifest, manifest.with_name('Cargo.lock')]
paths += sorted((ext / 'crate/src').rglob('*.rs'))
paths += sorted((ext / 'native/src').rglob('*.rs'))
paths += [release_dir / name for name in source_lock['files']]
for directory in [manifest.parent, *manifest.parent.parents]:
    paths += [directory / '.cargo' / name for name in ('config', 'config.toml')
              if (directory / '.cargo' / name).is_file()]
cargo_home = Path(env.get('CARGO_HOME', str(Path.home() / '.cargo')))
paths += [cargo_home / name for name in ('config', 'config.toml')
          if (cargo_home / name).is_file()]
compiler = Path(subprocess.check_output(['rustup', 'which', 'rustc', '--toolchain',
                                       args.toolchain], env=env, text=True).strip()).resolve()
paths.append(compiler)
paths += sorted((compiler.parent.parent / 'lib').glob('librustc_driver-*.so'))


def snapshot():
    result = {str(p.resolve()): digest(p) for p in sorted(set(paths))}
    for name in ('RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER',
                 'RUSTC_WORKSPACE_WRAPPER'):
        result['env:' + name] = hashlib.sha256(env.get(name, '<unset>').encode()).hexdigest()
    return result


check_release()
before = snapshot()
(run / 'inputs-before.json').write_text(json.dumps(before, indent=2) + '\n')
command = base + ['run', '--locked', '--offline', '--manifest-path', str(manifest)]
with (run / 'run.log').open('w') as log:
    result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
check_release()
after = snapshot()
(run / 'inputs-after.json').write_text(json.dumps(after, indent=2) + '\n')
text = (run / 'run.log').read_text()
counts = re.search(r'extension_native: slice_wrapper_cases=(\d+); array_wrapper_cases=(\d+); '
                   r'max_length_cases=(\d+); complete_buffers_on_ok_and_err=true', text)
vectors = re.search(r'extension_vectors: cases=(\d+); complete_success_and_error_states=true', text)
passed = (result.returncode == 0 and before == after and counts is not None
          and int(counts[1]) > 1000 and int(counts[2]) > 1000
          and vectors is not None and int(vectors[1]) > 1000
          and 'extension_defaults: builtin_codec_cases=2560; frontend_cases=512; constant_alias_values=true' in text
          and 'boundary_witnesses: 3 ' in text)
summary = {'status': 'passed' if passed else 'failed',
           'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'command': command, 'exit': result.returncode, 'inputs_match': before == after,
           'formal_evidence': False, 'run_directory': str(run),
           'input_snapshot_sha256': digest(run / 'inputs-before.json'),
           'log_sha256': digest(run / 'run.log'),
           'registry_archive_sha256': source_lock['sha256'],
           'release_files_checked_before_and_after': len(source_lock['files']),
           'slice_wrapper_cases': int(counts[1]) if counts else 0,
           'array_wrapper_cases': int(counts[2]) if counts else 0,
           'max_length_cases': int(counts[3]) if counts else 0,
           'vector_wrapper_cases': int(vectors[1]) if vectors else 0,
           'builtin_codec_cases': 2560 if passed else None,
           'default_frontend_cases': 512 if passed else None,
           'composed_roundtrip_cases': 3600 if passed else None,
           'semantic_boundary_witnesses': 3 if passed else None}
(run / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
raise SystemExit(0 if passed else 1)
