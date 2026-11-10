#!/usr/bin/env python3.11
"""Check the disclosed scalar macro outline against the pinned release.

The transformation specializes radix/types, outlines scalar loops, replaces
the iterator cursor observation by an explicit counter, and expands Option's
and_then into its ordinary match. Reviewed complete and partial u8/i8 front
ends are pinned separately. This does not prove original generic parser equivalence.
"""
from pathlib import Path
import re
import hashlib
import tarfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]

# Cargo's locked archive hash and the exact selected dependency bodies are inputs
# to extraction. Verify both the archive and the working registry source bytes.
lock = tomllib.loads((ROOT / 'verification/parser-harness/Cargo.lock').read_text())
util = next(p for p in lock['package'] if p['name'] == 'lexical-util')
archive = next((ROOT / '.work/cargo-home/registry/cache').glob('*/lexical-util-1.0.7.crate'))
if hashlib.sha256(archive.read_bytes()).hexdigest() != util['checksum']:
    raise SystemExit('lexical-util archive differs from parser Cargo.lock checksum')
with tarfile.open(archive) as crate:
    for name in ('digit.rs', 'error.rs', 'num.rs'):
        data = crate.extractfile('lexical-util-1.0.7/src/' + name).read()
        source = next((ROOT / '.work/cargo-home/registry/src').glob('*/lexical-util-1.0.7/src/' + name))
        if source.read_bytes() != data:
            raise SystemExit('Selected lexical-util source differs from locked archive: ' + name)


def tokens(text):
    text = re.sub(r'//[^\n]*', '', text)
    return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]', text)


release = (ROOT / '.work/source/src/algorithm.rs').read_text()
start = release.index('macro_rules! parse_1digit_checked {')
start = release.index(') => {{', start) + len(') => {{')
end = release.index('    }};', start)
body = release[start:end]
body = body.replace('NumberFormat::<FORMAT>::MANTISSA_RADIX', '10')
body = body.replace(
    'fmt_invalid_digit!($value, $iter, c, $start_index, $invalid_digit, true)',
    'return Err(Error::InvalidDigit(cursor - 1))')
body = body.replace('into_error!($overflow, $iter.cursor() - 1)',
                    'return Err(Error::Overflow(cursor - 1))')
body = body.replace('$value', 'value').replace('$iter', 'iter')
body = body.replace('$add_op', 'checked_add')
body = body.replace('as_cast(radix)', 'radix').replace('as_cast(digit)', 'digit')
body = body.replace('while let Some(&c) = iter.next() {',
                    'while let Some(&c) = iter.next() { cursor += 1;')
old = 'value.checked_mul(radix).and_then(|x| x.checked_add(digit))'
body = body.replace('value =\n                match ' + old,
                    'let combined = match value.checked_mul(radix) {'
                    ' Some(x) => x.checked_add(digit), None => None, };'
                    ' value = match combined')
# Rust permits the final unit-valued assignment without its semicolon; the
# standalone outline spells that statement terminator explicitly.
body = re.sub(r'(\n\s*})(\n\s*}\s*)$', r'\1;\2', body)
expected = 'let mut iter = bytes.iter();' + body + 'Ok(value)'
source = (ROOT / 'verification/parser-harness/src/lib.rs').read_text()
for name, operation, error in (
    ('checked_u32_from', 'checked_add', 'Overflow'),
    ('checked_i32_positive_from', 'checked_add', 'Overflow'),
    ('checked_i32_negative_from', 'checked_sub', 'Underflow'),
    ('checked_u8_from', 'checked_add', 'Overflow'),
):
    want = expected
    if name.startswith('checked_i32'):
        want = want.replace('let radix = 10;', 'let radix = 10u32;')
        want = want.replace('checked_mul(radix)', 'checked_mul(radix as i32)')
        want = want.replace('checked_add(digit)', operation + '(digit as i32)')
        want = want.replace('Error::Overflow', 'Error::' + error)
    elif name == 'checked_u8_from':
        want = want.replace('let radix = 10;', 'let radix = 10u32;')
        want = want.replace('checked_mul(radix)', 'checked_mul(radix as u8)')
        want = want.replace('checked_add(digit)', 'checked_add(digit as u8)')
    start = source.index('pub fn ' + name + '(')
    start = source.index('{', start) + 1
    end = source.index('\n}', start)
    if tokens(source[start:end]) != tokens(want):
        raise SystemExit('Outlined scalar loop differs from disclosed transformation: ' + name)

start = release.index('macro_rules! parse_1digit_unchecked {')
start = release.index(') => {{', start) + len(') => {{')
end = release.index('    }};', start)
unchecked = release[start:end]
unchecked = unchecked.replace('NumberFormat::<FORMAT>::MANTISSA_RADIX', '10u32')
unchecked = unchecked.replace(
    'fmt_invalid_digit!($value, $iter, c, $start_index, $invalid_digit, $is_end)',
    'return Err(Error::InvalidDigit(cursor - 1))')
unchecked = unchecked.replace('$value', 'value').replace('$iter', 'iter')
unchecked = unchecked.replace('$add_op', 'wrapping_add')
unchecked = unchecked.replace('as_cast(radix)', 'radix as u8')
unchecked = unchecked.replace('as_cast(digit)', 'digit as u8')
unchecked = unchecked.replace('while let Some(&c) = iter.next() {',
                              'while let Some(&c) = iter.next() { cursor += 1;')
want = 'let mut iter = bytes.iter();' + unchecked + 'Ok(value)'
start = source.index('pub fn unchecked_u8_from(')
start = source.index('{', start) + 1
end = source.index('\n}', start)
if tokens(source[start:end]) != tokens(want):
    raise SystemExit('Outlined unchecked u8 loop differs from disclosed transformation')


def harness_body(name):
    start = source.index('pub fn ' + name + '(')
    start = source.index('{', start) + 1
    return source[start:source.index('\n}', start)]


# Partial loops use the same release macro bodies. The caller's partial
# invalid-digit action returns the value before this byte and its absolute
# index; successful exhaustion returns the current cursor.
for name, kind, direction, partial in (
    ('checked_u8_partial_from', 'u8', 'add', True),
    ('checked_i8_positive_from', 'i8', 'add', False),
    ('checked_i8_negative_from', 'i8', 'sub', False),
    ('checked_i8_positive_partial_from', 'i8', 'add', True),
    ('checked_i8_negative_partial_from', 'i8', 'sub', True),
):
    want = expected.replace('let radix = 10;', 'let radix = 10u32;')
    want = want.replace('checked_mul(radix)', f'checked_mul(radix as {kind})')
    want = want.replace('checked_add(digit)', f'checked_{direction}(digit as {kind})')
    if direction == 'sub':
        want = want.replace('Error::Overflow', 'Error::Underflow')
    if partial:
        want = want.replace('return Err(Error::InvalidDigit(cursor - 1))',
                            'return Ok((value, cursor - 1))')
        want = want.replace('Ok(value)', 'Ok((value, cursor))')
    if tokens(harness_body(name)) != tokens(want):
        raise SystemExit('Outlined checked loop differs from release transformation: ' + name)

for name, kind, direction, partial in (
    ('unchecked_u8_partial_from', 'u8', 'add', True),
    ('unchecked_i8_positive_from', 'i8', 'add', False),
    ('unchecked_i8_negative_from', 'i8', 'sub', False),
    ('unchecked_i8_positive_partial_from', 'i8', 'add', True),
    ('unchecked_i8_negative_partial_from', 'i8', 'sub', True),
):
    want = 'let mut iter = bytes.iter();' + unchecked + 'Ok(value)'
    want = want.replace('as u8', f'as {kind}')
    want = want.replace('wrapping_add', f'wrapping_{direction}')
    if partial:
        want = want.replace('return Err(Error::InvalidDigit(cursor - 1))',
                            'return Ok((value, cursor - 1))')
        want = want.replace('Ok(value)', 'Ok((value, cursor))')
    if tokens(harness_body(name)) != tokens(want):
        raise SystemExit('Outlined unchecked loop differs from release transformation: ' + name)

# These eleven front-end bodies are separately reviewed default-format
# u8/i8 selections. Freeze exact structure without representing this check as
# a proof of equivalence to the generic release parser.
frontends = {
    'complete_u8': '''
    let cursor = if !bytes.is_empty() && bytes[0] == b'+' { 1 } else { 0 };
    complete_u8_from_cursor(bytes, cursor)
    ''',
    'complete_u8_from_cursor': '''
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 2 {
        return unchecked_u8_from(digits, 0, cursor);
    }
    let value = unchecked_u8_from(&digits[..2], 0, cursor)?;
    checked_u8_from(&digits[2..], value, cursor + 2)
    ''',
    'partial_u8': '''
    let cursor = if !bytes.is_empty() && bytes[0] == b'+' { 1 } else { 0 };
    partial_u8_from_cursor(bytes, cursor)
    ''',
    'partial_u8_from_cursor': '''
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 2 {
        return unchecked_u8_partial_from(digits, 0, cursor);
    }
    let (value, end) = unchecked_u8_partial_from(&digits[..2], 0, cursor)?;
    if end < cursor + 2 { return Ok((value, end)); }
    checked_u8_partial_from(&digits[2..], value, cursor + 2)
    ''',
    'sign_i8': '''
    if bytes.is_empty() { return (false, 0); }
    if bytes[0] == b'+' { return (false, 1); }
    if bytes[0] == b'-' { return (true, 1); }
    (false, 0)
    ''',
    'complete_i8': '''
    let (negative, cursor) = sign_i8(bytes);
    if negative { complete_i8_negative_from_cursor(bytes, cursor) }
    else { complete_i8_positive_from_cursor(bytes, cursor) }
    ''',
    'partial_i8': '''
    let (negative, cursor) = sign_i8(bytes);
    if negative { partial_i8_negative_from_cursor(bytes, cursor) }
    else { partial_i8_positive_from_cursor(bytes, cursor) }
    ''',
    'complete_i8_negative_from_cursor': '''
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_negative_from(digits, 0, cursor); }
    let value = unchecked_i8_negative_from(&digits[..1], 0, cursor)?;
    checked_i8_negative_from(&digits[1..], value, cursor + 1)
    ''',
    'complete_i8_positive_from_cursor': '''
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_positive_from(digits, 0, cursor); }
    let value = unchecked_i8_positive_from(&digits[..1], 0, cursor)?;
    checked_i8_positive_from(&digits[1..], value, cursor + 1)
    ''',
    'partial_i8_negative_from_cursor': '''
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_negative_partial_from(digits, 0, cursor); }
    let (value, end) = unchecked_i8_negative_partial_from(&digits[..1], 0, cursor)?;
    if end < cursor + 1 { return Ok((value, end)); }
    checked_i8_negative_partial_from(&digits[1..], value, cursor + 1)
    ''',
    'partial_i8_positive_from_cursor': '''
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_positive_partial_from(digits, 0, cursor); }
    let (value, end) = unchecked_i8_positive_partial_from(&digits[..1], 0, cursor)?;
    if end < cursor + 1 { return Ok((value, end)); }
    checked_i8_positive_partial_from(&digits[1..], value, cursor + 1)
    ''',
}
for name, want in frontends.items():
    start = source.index('pub fn ' + name + '(')
    start = source.index('{', start) + 1
    end = source.index('\n}', start)
    if tokens(source[start:end]) != tokens(want):
        raise SystemExit('Reviewed u8/i8 front-end changed: ' + name)

# The front-end slice is reviewed separately from the exact loop outlines.
# Pin release dispatch premises and dependency u8/i8 digit thresholds.
num_source = next((ROOT / '.work/cargo-home/registry/src').glob('*/lexical-util-1.0.7/src/num.rs')).read_text()
for expected_fragment in (
    'u8 false ;',
    'i8 true ;',
    'mem::size_of::<Self>() * 2 - Self::IS_SIGNED as usize',
    'integer_impl! { u8 u16 u32 u64 u128 i8 i16 i32 i64 i128 usize isize }',
):
    if expected_fragment not in num_source:
        raise SystemExit('u8/i8 overflow-digit premise changed in lexical-util')
for expected_fragment in (
    'let overflow_digits = T::overflow_digits(radix);',
    'let cannot_overflow = iter.as_slice().len() <= overflow_digits;',
    'if cannot_overflow && is_negative {',
    '} if cannot_overflow {',
    'if let Some(mut small) = $iter.take_n($overflow_digits) {',
):
    if expected_fragment not in release:
        raise SystemExit('selected parser dispatch premise changed in release')

print('Four checked and one unchecked scalar loops match disclosed release macro outlines')
print('Ten additional partial/signed scalar loops match disclosed release macro outlines')
print('Pinned u8/i8 dispatch premises and reviewed complete/partial front-end adaptations')
