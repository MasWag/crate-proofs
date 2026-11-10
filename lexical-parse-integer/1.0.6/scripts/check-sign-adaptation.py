#!/usr/bin/env python3.11
"""Check the sign helper against the locked release macro outline.

The adaptation exposes the current byte, cursor, and three computed format/type
flags as arguments. Its pair result records cursor mutation on success and
error. Equivalence of the explicit arguments to a concrete FORMAT/Bytes call
remains a separate release-correspondence obligation.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
release = (ROOT / '.work/source/src/algorithm.rs').read_text()
source = (ROOT / 'verification/sign-harness/src/lib.rs').read_text()


def tokens(text):
    text = re.sub(r'//[^\n]*', '', text)
    return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]', text)


start = release.index('macro_rules! parse_sign {')
start = release.index(') => {', start) + len(') => {')
end = release.index('    };', start)
expected = release[start:end]
expected = expected.replace('$byte.integer_iter().first()', 'byte')
expected = expected.replace("Some(&b'+')", "Some(b'+')")
expected = expected.replace("Some(&b'-')", "Some(b'-')")
expected = expected.replace('unsafe { $byte.step_unchecked() };\n                Ok(false)',
                            '(Ok(false), cursor + 1)')
expected = expected.replace('unsafe { $byte.step_unchecked() };\n                Ok(true)',
                            '(Ok(true), cursor + 1)')
expected = expected.replace('Err(Error::$invalid_positive($byte.cursor()))',
                            '(Err(Error::InvalidPositiveSign(cursor)), cursor)')
expected = expected.replace('Err(Error::$missing($byte.cursor()))',
                            '(Err(Error::MissingSign(cursor)), cursor)')
expected = expected.replace('$no_positive', 'no_positive')
expected = expected.replace('$is_signed', 'is_signed')
expected = expected.replace('$required', 'required')
expected = expected.replace('_ => Ok(false)', '_ => (Ok(false), cursor)')
if '$' in expected:
    raise SystemExit('unreviewed sign macro parameter remains')

start = source.index('pub fn parse_sign_state(')
start = source.index('{', start) + 1
depth = 1
for end in range(start, len(source)):
    depth += (source[end] == '{') - (source[end] == '}')
    if depth == 0:
        break
else:
    raise SystemExit('unclosed sign harness body')
if tokens(source[start:end]) != tokens(expected):
    left, right = tokens(expected), tokens(source[start:end])
    mismatch = next((i for i, (a, b) in enumerate(zip(left, right)) if a != b), min(len(left), len(right)))
    print('expected:', left[max(0, mismatch - 8):mismatch + 12])
    print('harness: ', right[max(0, mismatch - 8):mismatch + 12])
    raise SystemExit('sign helper differs from disclosed release macro outline')
print('sign helper matches release macro branch/order after explicit state adaptation')
