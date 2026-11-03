#!/usr/bin/env python3
"""Derive the Kani library from the unchanged restored release, annotations only."""
import argparse, hashlib
from pathlib import Path
root = Path(__file__).resolve().parents[1]
source = root.parent / '.work/source/src/lib.rs'
original = source.read_bytes()
# Registry release source checked by the enclosing version's source.lock.json.
expected = '80efd99de651687389caf00a1d55b79d157ee1db1ddc8344d0d65418adcd36dc'
assert hashlib.sha256(original).hexdigest() == expected, 'release lib.rs hash changed'
text = original.decode()
needle = '    pub fn unwrap(self)'
assert text.count(needle) == 1
annotation = '''    #[cfg_attr(kani, kani::requires(BlockSize::USIZE == 16 && matches!(&self, PaddedData::Pad { blocks, .. } if blocks.len() <= 2)))]
    #[cfg_attr(kani, kani::ensures(|result| crate::contracts::unwrap_ok(result, old(crate::contracts::snapshot(&self)))))]
'''
text = text.replace(needle, annotation + needle)
text += '\n#[cfg(kani)]\nmod contracts;\n'
target = root / 'src/lib.rs'
parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
if args.check:
    assert target.read_text() == text, 'derived Kani source changed'
else:
    target.write_text(text)
