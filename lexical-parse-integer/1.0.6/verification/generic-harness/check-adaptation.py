#!/usr/bin/env python3.11
"""Pin the checked scalar release macro outline and its selected dependency.

Reviewed adaptations: runtime radix parameter in place of FORMAT constant, slice
iterator/cursor counter in place of DigitsIter, match in place of Option.and_then,
and direct complete-mode error return in place of fmt_invalid_digit. This is a
source comparison, not a formal equivalence proof of raw iterator behavior.
"""
from pathlib import Path
import hashlib
import re
import tarfile
import tomllib

ROOT = Path(__file__).resolve().parents[2]
release = (ROOT / '.work/source/src/algorithm.rs').read_text()
harness = (ROOT / 'verification/generic-harness/src/lib.rs').read_text()

def tokens(text):
    text = re.sub(r'//[^\n]*', '', text)
    return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]', text)

def macro_body(src, name):
    start = src.index('macro_rules! ' + name + ' {')
    start = src.index(') => {{', start) + len(') => {{')
    return src[start:src.index('    }};', start)]

source = macro_body(release, 'parse_1digit_checked')
source = source.replace('let radix = NumberFormat::<FORMAT>::MANTISSA_RADIX;', '')
source = source.replace('fmt_invalid_digit!($value, $iter, c, $start_index, $invalid_digit, true)',
                        'return Err(Error::InvalidDigit(cursor - 1))')
source = source.replace('into_error!($overflow, $iter.cursor() - 1)',
                        'return Err(Error::$error(cursor - 1))')
source = source.replace('$value', 'value').replace('$iter', 'iter')
source = source.replace('as_cast(radix)', 'radix as $ty')
source = source.replace('as_cast(digit)', 'digit as $ty')
source = source.replace('while let Some(&c) = iter.next() {',
                        'while let Some(&c) = iter.next() { cursor += 1;')
source = source.replace('value =\n                match value.checked_mul(radix as $ty).and_then(|x| x.$add_op(digit as $ty))',
                        'let combined = match value.checked_mul(radix as $ty) {'
                        ' Some(x) => x.$add_op(digit as $ty), None => None, };'
                        ' value = match combined')
source = re.sub(r'(\n\s*})(\n\s*}\s*)$', r'\1;\2', source)
expected = 'let mut iter = bytes.iter();' + source + 'Ok(value)'

for macro, operation, error, end in [
    ('unsigned_checked', 'checked_add', 'Overflow', 'macro_rules! signed_checked'),
    ('signed_checked', '$operation', '$error', 'unsigned_checked!(checked_u8')]:
    start = harness.index('macro_rules! ' + macro)
    body = harness[harness.index('let mut iter = bytes.iter();', start):harness.index('Ok(value)', start) + len('Ok(value)')]
    if end not in harness[start:]:
        raise SystemExit('harness macro boundary missing: ' + macro)
    want = expected.replace('$add_op', operation).replace('$error', error)
    if tokens(body) != tokens(want):
        import difflib
        print('\n'.join(difflib.unified_diff(tokens(want), tokens(body), fromfile='release-adaptation', tofile=macro)))
        raise SystemExit('generic checked macro differs from disclosed release transformation: ' + macro)

# Every intended primitive width and signed direction is instantiated once.
want_calls = [f'unsigned_checked!(checked_{t}, {t});' for t in
              ('u8', 'u16', 'u32', 'u64', 'u128', 'usize')]
want_calls += [f'signed_checked!(checked_{t}_{direction}, {t}, checked_{op}, {err});'
               for t in ('i8', 'i16', 'i32', 'i64', 'i128', 'isize')
               for direction, op, err in (('positive', 'add', 'Overflow'), ('negative', 'sub', 'Underflow'))]
for call in want_calls:
    if harness.count(call) != 1:
        raise SystemExit('missing or duplicate specialization: ' + call)

partial = (ROOT / 'verification/generic-harness/src/partial.rs').read_text()
partial_expected = expected.replace('return Err(Error::InvalidDigit(cursor - 1))',
                                    'return Ok((value, cursor - 1))')
partial_expected = partial_expected.replace('Ok(value)', 'Ok((value, cursor))')
for macro, operation, error in [
    ('unsigned_partial', 'checked_add', 'Overflow'),
    ('signed_partial', '$operation', '$error')]:
    start = partial.index('macro_rules! ' + macro)
    body = partial[partial.index('let mut iter = bytes.iter();', start):
                   partial.index('Ok((value, cursor))', start) + len('Ok((value, cursor))')]
    want = partial_expected.replace('$add_op', operation).replace('$error', error)
    if tokens(body) != tokens(want):
        import difflib
        print('\n'.join(difflib.unified_diff(tokens(want), tokens(body),
                                             fromfile='release-partial-adaptation', tofile=macro)))
        raise SystemExit('generic partial macro differs from disclosed release transformation: ' + macro)
partial_calls = [f'unsigned_partial!(checked_{t}_partial, {t});' for t in
                 ('u8', 'u16', 'u32', 'u64', 'u128', 'usize')]
partial_calls += [f'signed_partial!(checked_{t}_{direction}_partial, {t}, checked_{op}, {err});'
                  for t in ('i8', 'i16', 'i32', 'i64', 'i128', 'isize')
                  for direction, op, err in (('positive', 'add', 'Overflow'),
                                              ('negative', 'sub', 'Underflow'))]
for call in partial_calls:
    if partial.count(call) != 1:
        raise SystemExit('missing or duplicate partial specialization: ' + call)

lock = tomllib.loads((ROOT / 'verification/generic-harness/Cargo.lock').read_text())
util = next(p for p in lock['package'] if p['name'] == 'lexical-util')
archive = next((ROOT / '.work/cargo-home/registry/cache').glob('*/lexical-util-1.0.7.crate'))
if hashlib.sha256(archive.read_bytes()).hexdigest() != util['checksum']:
    raise SystemExit('lexical-util archive differs from generic Cargo.lock checksum')
with tarfile.open(archive) as crate:
    for name in ('digit.rs', 'error.rs', 'num.rs'):
        data = crate.extractfile('lexical-util-1.0.7/src/' + name).read()
        path = next((ROOT / '.work/cargo-home/registry/src').glob('*/lexical-util-1.0.7/src/' + name))
        if path.read_bytes() != data:
            raise SystemExit('selected lexical-util source differs from locked archive: ' + name)

for name in ('DigitSpecs.lean', 'GenericScalarSpecs.lean'):
    parser = ROOT / 'aeneas/profiles/parser/proofs' / name
    for profile in ('generic_checked', 'generic_partial'):
        generic = ROOT / 'aeneas/profiles' / profile / 'proofs' / name
        if generic.read_bytes() != parser.read_bytes():
            raise SystemExit(profile + ' pure spec differs from independently authored parser copy: ' + name)
print('generic checked and partial macro adaptations, specializations, dependency and pure specs match pinned inputs')
