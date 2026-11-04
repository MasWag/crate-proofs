#!/usr/bin/env python3
"""Prepare a registry-named recording fixture from accepted extension sources."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

EXT = Path(__file__).resolve().parent.parent
ROOT = EXT.parent
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('accepted_run', type=Path)
args = parser.parse_args()
run = args.accepted_run.resolve()
summary = json.loads((run / 'summary.json').read_text())
assert summary['status'] == 'passed' and summary['inputs_match']
before = {}
for line in (run / 'inputs-before.sha256').read_text().splitlines():
    value, path = line.split('  ', 1)
    if not path.startswith('env:'):
        before[Path(path).resolve()] = value


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


source = EXT / 'crate/src'
destination = HERE / 'crate/src'
destination.mkdir(parents=True, exist_ok=True)
records = []
for file in sorted(source.glob('*.rs')):
    assert digest(file) == before[file.resolve()], file
    text = file.read_text()
    if file.name == 'lib.rs':
        opening = 'macro_rules! define_decode_into_const {\n    ($($constness:ident)?) => {\n'
        ending = ('\n    };\n}\n\n#[cfg(creusot)]\ndefine_decode_into_const!();\n'
                  '#[cfg(not(creusot))]\ndefine_decode_into_const!(const);\n')
        assert text.count(opening) == text.count(ending) == 1
        text = text.replace(opening, '').replace(ending, '')
        assert text.count('pub $($constness)? fn decode_into_const') == 1
        text = text.replace('pub $($constness)? fn decode_into_const', 'pub fn decode_into_const')
        text = text.replace('// Preserve the native const API while allowing erased ghost calls in the\n'
                            '// verification instance. Both instances use exactly this one function body.',
                            '// Publication fixture: expanded non-const verification instance.\n'
                            '// The accepted application workspace retains its native const decoder.')
    target = destination / file.name
    target.write_text(text)
    records.append({'file': file.name, 'accepted_sha256': digest(file),
                    'recording_sha256': digest(target),
                    'byte_identical': file.read_bytes() == target.read_bytes()})
prior = ROOT / 'verification/publication/crate'
for name in ('Cargo.toml', 'Cargo.lock', 'why3find.json'):
    shutil.copyfile(prior / name, HERE / 'crate' / name)
(HERE / 'crate/proofs.toml').write_text(
    '[report]\ntitle = "bs58 0.5.1: selected contracts in a Creusot proof fork"\n\n'
    '[tool]\nname = "creusot"\nversion = "0.13.0"\ntarget = "annotated"\n')
comparison = json.loads((ROOT / 'verification/publication/registry-source-comparison.json').read_text())
registry = ROOT / '.work/tools/cargo/registry/src'
for name, package in comparison['packages'].items():
    roots = list(registry.glob(f'*/{name}-{package["version"]}/src'))
    assert len(roots) == 1, (name, roots)
    actual = {str(p.relative_to(roots[0])): digest(p) for p in roots[0].rglob('*.rs')}
    assert actual == package['files'], name
(HERE / 'registry-source-comparison.json').write_text(json.dumps(comparison, indent=2) + '\n')
descriptor = {'accepted_run': str(run), 'accepted_summary_sha256': digest(run / 'summary.json'),
              'source_files': records,
              'transformations': ['Package identity is bs58 0.5.1 for the service, not the unchanged registry release.',
                                  'Expand only the fixed-array macro into its Creusot ordinary pub fn; body/annotations unchanged.',
                                  'Use exact registry creusot-std 0.13.0; all 127 Rust model/proc sources rechecked.',
                                  'Use direct SMT search without compute preprocessing for the unmodified recorder importer.'],
              'scope': 'Recording requires its own successful fresh run; preparing this fixture is not a proof.'}
(HERE / 'source-transformation.json').write_text(json.dumps(descriptor, indent=2) + '\n')
print(json.dumps({'fixture': str(HERE / 'crate'), 'files': len(records),
                  'byte_identical_files': sum(r['byte_identical'] for r in records)}, indent=2))
