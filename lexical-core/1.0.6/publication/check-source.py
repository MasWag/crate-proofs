#!/usr/bin/env python3.11
"""Check this publication package selects the same documented adapted Rust bytes."""
from pathlib import Path
import hashlib
import json
import re
import tomllib
ROOT = Path(__file__).resolve().parent
record = json.loads((ROOT / 'source-correspondence.json').read_text())
manifest = tomllib.loads((ROOT / 'Cargo.toml').read_text())
assert manifest['package']['name'] == 'lexical-core' and manifest['package']['version'] == '1.0.6'
assert manifest['lib']['name'] == 'lexical_core'
selected = (ROOT / manifest['lib']['path']).resolve()
assert selected == (ROOT / record['library_path']).resolve()
assert hashlib.sha256(selected.read_bytes()).hexdigest() == record['library_sha256']
actual = selected.read_text()
upstream = (ROOT / '.work/upstream-source/src/lib.rs').read_text()
for name in ['write', 'write_with_options', 'parse', 'parse_partial', 'parse_with_options', 'parse_partial_with_options']:
    pattern = r'pub fn ' + name + r'(?=[<(])[^{}]+\{[^{}]+\}'
    assert re.search(pattern, actual).group() == re.search(pattern, upstream).group(), name
model = ROOT / 'proofs/Facade.lean'
assert hashlib.sha256(model.read_bytes()).hexdigest() == record['model_sha256']
assert 'namespace lexical_core\n' in model.read_text()
assert not re.search(r'(?m)^\s*(?:axiom|opaque|partial\s+def)\b|\b(?:sorry|admit)\b', model.read_text())
print('Publication Cargo library selects the exact documented adapted source; all six release definitions match; fresh lexical_core model bytes pinned. No release-trait equivalence claim.')
