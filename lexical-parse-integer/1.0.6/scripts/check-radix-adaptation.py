#!/usr/bin/env python3
"""Check explicit-radix SWAR bodies against the locked release source."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / '.work/source/src/algorithm.rs'
HARNESS = ROOT / 'verification/radix-harness/src/lib.rs'
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
        text = text.replace('<const FORMAT: u128>(', '(radix: u32, ', 1)
        if name == 'parse_8digits':
            text = text.replace('let radix = NumberFormat::<{ FORMAT }>::MANTISSA_RADIX as u64;',
                                'let radix = radix as u64;', 1)
        else:
            text = text.replace('let radix = NumberFormat::<{ FORMAT }>::MANTISSA_RADIX;\n    ', '', 1)
        if 'NumberFormat' in text or 'FORMAT' in text:
            raise ValueError('unreviewed format dependence in ' + name)
        functions.append(text)
    return '// Explicit radix argument replaces locked release format radix lookup.\n' + '\n\n'.join(functions) + '\n'


def main():
    want = expected()
    if len(sys.argv) == 2 and sys.argv[1] == '--write':
        HARNESS.parent.mkdir(parents=True, exist_ok=True)
        HARNESS.write_text(want)
    if HARNESS.read_text() != want:
        raise SystemExit('radix SWAR harness differs from exact release body adaptation')
    print('radix harness matches four release bodies after explicit radix parameterization')


if __name__ == '__main__':
    main()
