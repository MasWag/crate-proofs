#!/usr/bin/env python3
"""Materialize and check one disclosed release-body adaptation; never edit release."""
import argparse, hashlib
from pathlib import Path
r = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(); p.add_argument('--prepare', action='store_true'); a = p.parse_args()
s = r/'.work/source'; d = r/'.work/adapted'
old = '        self.map_or_else(default, f)'
new = '        match self { Some(value) => f(value), None => default() }'
body = (s/'src/impl.rs').read_text()
assert body.count(old) == 1
expected = {'lib.rs': (s/'src/lib.rs').read_text(), 'impl.rs': body.replace(old,new)}
if a.prepare:
    d.mkdir(parents=True,exist_ok=True)
    for name,text in expected.items(): (d/name).write_text(text)
for name,text in expected.items():
    assert (d/name).read_text() == text, 'adaptation mismatch: '+name
assert {p.name for p in d.iterdir()} == set(expected)
print('Exact adaptation checked: only map_or_else2 delegated expression becomes direct match.')
for name in expected:
    for label,path in [('original',s/'src'/name),('adapted',d/name)]:
        print(label, name, hashlib.sha256(path.read_bytes()).hexdigest())
