#!/usr/bin/env python3.11
"""Check the adapted copy differs from the locked release at one Rust arm."""
from pathlib import Path
import tomllib

ROOT = Path(__file__).resolve().parents[2]
RELEASE = ROOT / '.work/source'
ADAPTED = Path(__file__).resolve().parent

old_arm = 'Err(error) => core::panic!("{}", error.description()),'
new_arm = 'Err(_error) => self.build_unchecked(),'
original = (RELEASE / 'src/options.rs').read_text()
if original.count(old_arm) != 1:
    raise SystemExit('Release panic arm changed')
if (ADAPTED / 'src/options.rs').read_text() != original.replace(old_arm, new_arm):
    raise SystemExit('Adapted options.rs differs beyond the disclosed panic arm')

manifest = (RELEASE / 'Cargo.toml').read_text()
if manifest.count('name = "lexical-parse-integer"') != 1 or manifest.count('name = "lexical_parse_integer"') != 1:
    raise SystemExit('Release manifest identity changed')
want = manifest.replace('name = "lexical-parse-integer"',
                        'name = "lexical-parse-integer-options-strict-adapted"', 1)
want = want.replace('name = "lexical_parse_integer"',
                    'name = "lexical_parse_integer_options_strict_adapted"', 1)
want += ('\n[workspace]\n\n[dev-dependencies.release]\n'
         'package = "lexical-parse-integer"\npath = "../.."\n'
         'features = ["power-of-two"]\n\n[[test]]\n'
         'name = "strict_compare"\npath = "tests/strict_compare.rs"\n')
if (ADAPTED / 'Cargo.toml').read_text() != want:
    raise SystemExit('Adapted Cargo.toml differs beyond independent workspace/test wiring')

original_files = {p.relative_to(RELEASE) for p in RELEASE.rglob('*') if p.is_file()}
allowed_changes = {Path('Cargo.toml'), Path('Cargo.lock'), Path('src/options.rs')}
for relative in original_files - allowed_changes:
    if (ADAPTED / relative).read_bytes() != (RELEASE / relative).read_bytes():
        raise SystemExit(f'Adapted release file changed: {relative}')
actual_files = {p.relative_to(ADAPTED) for p in ADAPTED.rglob('*')
                if p.is_file() and 'target' not in p.relative_to(ADAPTED).parts}
allowed_additions = {Path('tests/strict_compare.rs'), Path('check-adaptation.py')}
if actual_files - original_files != allowed_additions:
    raise SystemExit(f'Unexpected adapted files: {actual_files - original_files}')

def utility_checksum(lock):
    matches = [p for p in tomllib.loads(lock.read_text())['package']
               if p['name'] == 'lexical-util' and p['version'] == '1.0.7']
    if len(matches) != 1:
        raise SystemExit('Expected one lexical-util 1.0.7 dependency')
    return matches[0]['checksum']

if utility_checksum(ADAPTED / 'Cargo.lock') != utility_checksum(ROOT / 'Cargo.lock'):
    raise SystemExit('Adapted dependency checksum differs from release lock')
print('Adapted release src differs only at build_strict Err arm; manifest and locked dependency checked')
