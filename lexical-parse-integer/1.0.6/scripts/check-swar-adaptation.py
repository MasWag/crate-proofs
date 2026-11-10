#!/usr/bin/env python3
"""Check the decimal SWAR harness against the locked release's four bodies."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / '.work/source/src/algorithm.rs'
HARNESS = ROOT / 'verification/harness/src/lib.rs'
NAMES = ('is_4digits', 'parse_4digits', 'is_8digits', 'parse_8digits')


def body(name, source):
    match = re.search(r'pub fn ' + name + r'<const FORMAT: u128>\(', source)
    if not match:
        raise ValueError('missing release function ' + name)
    start = match.start()
    opening = source.index('{', source.index('->', start))
    depth = 0
    for i in range(opening, len(source)):
        depth += (source[i] == '{') - (source[i] == '}')
        if depth == 0:
            return source[start:i + 1]
    raise ValueError('unclosed release function ' + name)


def expected():
    source = SOURCE.read_text()
    functions = []
    for name in NAMES:
        text = body(name, source)
        text = text.replace('<const FORMAT: u128>', '')
        text = text.replace('NumberFormat::<{ FORMAT }>::MANTISSA_RADIX', '10u32')
        if 'NumberFormat' in text or 'FORMAT' in text:
            raise ValueError('unreviewed format dependence in ' + name)
        functions.append(text)
    return '// Checked decimal specialization of locked release SWAR bodies.\n' + '\n\n'.join(functions) + '\n'


def main():
    want = expected()
    if len(sys.argv) == 2 and sys.argv[1] == '--write':
        HARNESS.parent.mkdir(parents=True, exist_ok=True)
        HARNESS.write_text(want)
    if HARNESS.read_text() != want:
        raise SystemExit('SWAR harness differs from exact decimal specialization of release')
    print('SWAR harness matches four release bodies after const radix 10 specialization')


if __name__ == '__main__':
    main()
