#!/usr/bin/env python3.11
"""Check exact facade definitions and method signatures against pinned releases."""
import hashlib
import json
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
metadata = json.loads((ROOT / 'verification/facade/adaptation.json').read_text())
original = (ROOT / '.work/source/src/lib.rs').read_text()
adapted = (ROOT / 'verification/facade/src/lib.rs').read_text()
api_path = ROOT / metadata['release_api_macro_path']
assert hashlib.sha256(api_path.read_bytes()).hexdigest() == metadata['release_api_macro_sha256']
api = api_path.read_text()
for name in ['write', 'write_with_options', 'parse', 'parse_partial', 'parse_with_options', 'parse_partial_with_options']:
    pattern = r'pub fn ' + name + r'(?=[<(])[^{}]+\{[^{}]+\}'
    assert re.search(pattern, original).group() == re.search(pattern, adapted).group(), name
for name in ['from_lexical', 'from_lexical_partial', 'from_lexical_with_options', 'from_lexical_partial_with_options', 'to_lexical', 'to_lexical_with_options']:
    pattern = r'fn ' + name + r'(?=[<(])[^;]+;'
    expected = re.search(pattern, api).group().replace('lexical_util::result::Result', 'Result')
    actual = re.search(pattern, adapted).group()
    assert ''.join(expected.split()).replace(',)', ')') == ''.join(actual.split()).replace(',)', ')'), name
assert api.count('pub trait FromLexical: lexical_util::num::Number') == 1
assert api.count('pub trait FromLexicalWithOptions: lexical_util::num::Number') == 1
assert api.count('lexical_util::constants::FormattedSize + lexical_util::num::Number') == 2
assert 'type Options: lexical_util::options::ParseOptions;' in api
assert 'type Options: lexical_util::options::WriteOptions;' in api
assert 'lexical_util::num::Number' not in adapted
assert 'type Options;' in adapted
print('Exact six release definitions and six required method signatures checked; unused trait bounds deliberately erased. No formal release-model equivalence claim.')
