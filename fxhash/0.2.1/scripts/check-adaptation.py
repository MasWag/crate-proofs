#!/usr/bin/env python3
"""Materialize and check the disclosed source-level proof adaptations."""
import argparse
import hashlib
from pathlib import Path
root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--prepare', action='store_true')
args = parser.parse_args()
original = root / '.work/source/lib.rs'
adapted = root / '.work/adapted/lib.rs'
old = 'self.rotate_left(ROTATE).bitxor(word).wrapping_mul($key)'
new = '(self.rotate_left(ROTATE) ^ word).wrapping_mul($key)'
source = original.read_text()
if source.count(old) != 1:
    raise SystemExit('expected exactly one release expression')
expected = source.replace(old, new)
for before, after in [
    ('fn write(hash: usize, bytes: &[u8]) -> usize {',
     'fn write_native(hash: usize, bytes: &[u8]) -> usize {'),
    ('self.hash = write(self.hash, bytes);',
     'self.hash = write_native(self.hash, bytes);'),
]:
    if expected.count(before) != (2 if before.startswith('fn write(') else 1):
        raise SystemExit('unexpected release occurrence count: ' + before)
    expected = expected.replace(before, after)
for before, after, count in [
    ('NativeEndian::read_u32(bytes)',
     'u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])', 2),
    ('NativeEndian::read_u64(bytes)',
     'u64::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7]])', 1),
]:
    if expected.count(before) != count:
        raise SystemExit('unexpected release read occurrence count: ' + before)
    expected = expected.replace(before, after)
anchor = 'use std::collections::{HashMap, HashSet};'
if expected.count(anchor) != 1:
    raise SystemExit('unexpected source import anchor count')
expected = expected.replace(anchor,
    '#[cfg(not(target_endian = "little"))]\n'
    'compile_error!("fxhash verification adaptation requires little-endian target");\n'
    + anchor)
if args.prepare:
    adapted.parent.mkdir(parents=True, exist_ok=True)
    adapted.write_text(expected)
if adapted.read_text() != expected:
    raise SystemExit('derived Rust differs from reviewed source adaptations')
print('Original SHA256:', hashlib.sha256(original.read_bytes()).hexdigest())
print('Adapted SHA256:', hashlib.sha256(adapted.read_bytes()).hexdigest())
