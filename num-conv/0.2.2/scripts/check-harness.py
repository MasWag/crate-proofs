#!/usr/bin/env python3
"""Check exact public-call correspondence with the checksum-locked release pair ledger."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parent.parent
source = (root / '.work/source/src/lib.rs').read_text()
widen = source.rsplit('impl_widen! {', 1)[1].split('}', 1)[0]
truncate = source.rsplit('impl_truncate! {', 1)[1].split('}', 1)[0]
expected = set()
for src, destinations in re.findall(r'(\w+)\s*=>\s*([^;]+);', widen):
    for dst in re.findall(r'\w+', destinations):
        expected.update((method, src, dst) for method in ('widen', 'extend'))
for sources, dst in re.findall(r'([^;]+)\s*=>\s*(\w+);', truncate):
    for src in re.findall(r'\w+', sources):
        expected.update((method, src, dst) for method in ('truncate', 'saturating_truncate', 'checked_truncate'))
assert len(expected) == 180
harness = (root / 'verification/api.rs').read_text()
assert '#[path = "../.work/source/src/lib.rs"]\npub mod release;' in harness
assert 'pub use release::{Extend, Truncate, Widen};' in harness
assert re.findall(r'crate::[A-Za-z_0-9:]+', source) == []  # crate::{...} reexport checked below
assert 'pub use crate::{Extend as _, Truncate as _, Widen as _};' in source
pattern = r'pub fn (\w+)\(x: (\w+)\) -> (Option<\w+>|\w+) \{ release::(\w+)::(\w+)\(x\) \}'
remainder = re.sub(pattern, '', harness)
expected_header = '//! Verification-only concrete public calls into the unchanged release library.\n#![allow(deprecated, unused_attributes)]\n#![no_std]\n#[path = "../.work/source/src/lib.rs"]\npub mod release;\npub use release::{Extend, Truncate, Widen};\n'
assert re.sub(r'\s+', '', remainder) == re.sub(r'\s+', '', expected_header)
actual = set()
for name, src, result, trait, method in re.findall(pattern, harness):
    dst = result.removeprefix('Option<').removesuffix('>')
    assert name == f'{method}_{src}_{dst}'
    assert trait == {'widen': 'Widen', 'extend': 'Extend', 'truncate': 'Truncate', 'saturating_truncate': 'Truncate', 'checked_truncate': 'Truncate'}[method]
    assert result.startswith('Option<') == (method == 'checked_truncate')
    actual.add((method, src, dst))
assert actual == expected
assert len(re.findall(pattern, harness)) == 180
ledger = json.loads((root / 'verification/api-map.json').read_text())
assert {(x['method'], x['source_type'], x['destination_type']) for x in ledger} == expected
assert len(ledger) == 180
print('All 180 public-call wrappers exactly match the unchanged release pair declarations.')
