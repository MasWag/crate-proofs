#!/usr/bin/env python3
"""Reproduce the narrow iterator-any to index-loop source adaptation."""
from pathlib import Path
import hashlib, json, sys
r=Path(__file__).resolve().parents[1]
raw=(r/'.work/source/src/lib.rs').read_bytes()
lock=json.loads((r/'source.lock.json').read_text())
expected=lock['files']['src/lib.rs']['sha256']
assert hashlib.sha256(raw).hexdigest()==expected, 'Release source hash mismatch'
s=raw.decode()
def replace_once(s, old, new):
    assert s.count(old)==1, f'Expected one adaptation site, found {s.count(old)}'
    return s.replace(old,new)
s=replace_once(s,'if strict && block[s..bs - 1].iter().any(|&v| v != n) {\n            return Err(Error);\n        }','''if strict {
            let mut i = s;
            while i < bs - 1 {
                if block[i] != n { return Err(Error); }
                i += 1;
            }
        }''')
s=replace_once(s,'if block[s..bs - 1].iter().any(|&v| v != 0) {\n            return Err(Error);\n        }','''let mut i = s;
        while i < bs - 1 {
            if block[i] != 0 { return Err(Error); }
            i += 1;
        }''')
p=r/'verification/harness/src/lib.rs'
s=s.replace('include_str!("../README.md")','include_str!("../../../.work/source/README.md")')
if '--check' in sys.argv:
    assert p.read_text()==s, 'Derived harness source differs from reproducible adaptation'
else:
    p.write_text(s)
