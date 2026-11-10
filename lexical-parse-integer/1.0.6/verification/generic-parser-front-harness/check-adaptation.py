#!/usr/bin/env python3.11
"""Pin the release-derived scalar frontend adaptation and its inputs.

This compares exact selected macro templates and the reviewed safe slice/cursor
frontend. It does not prove equivalence of the original raw iterator/macro API.
"""
from pathlib import Path
import hashlib
import re
import tarfile
import tomllib

ROOT = Path(__file__).resolve().parents[2]
FRONT = ROOT / 'verification/generic-parser-front-harness'
source = (FRONT / 'src/lib.rs').read_text()
release = (ROOT / '.work/source/src/algorithm.rs').read_text()
util_root = next((ROOT / '.work/cargo-home/registry/src').glob('*/lexical-util-1.0.7'))
util_num = (util_root / 'src/num.rs').read_text()

def tokens(s):
    s = re.sub(r'//[^\n]*', '', s)
    return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]', s)

def fail_compare(label, actual, expected):
    if tokens(actual) != tokens(expected):
        import difflib
        print('\n'.join(difflib.unified_diff(tokens(expected), tokens(actual),
                                             fromfile='reviewed adaptation', tofile=label)))
        raise SystemExit('source changed outside reviewed adaptation: ' + label)

def balanced_body(text, marker):
    at = text.index(marker)
    start = text.index('{', at)
    depth = 1
    for i in range(start + 1, len(text)):
        if text[i] == '{':
            depth += 1
        elif text[i] == '}':
            depth -= 1
            if depth == 0:
                return text[start + 1:i]
    raise SystemExit('unclosed body: ' + marker)

def macro_body(text, name):
    at = text.index('macro_rules! ' + name + ' {')
    at = text.index(') => {{', at) + len(') => {{')
    return text[at:text.index('}};', at)]

# The source-selected no_multi_digit=true path takes overflow_digits bytes
# through the unchecked scalar macro, then invokes the checked scalar macro.
checked_path = macro_body(release, 'parse_digits_checked')
for text in ('take_n($overflow_digits)', 'parse_digits_unchecked!', 'parse_1digit_checked!'):
    if text not in checked_path:
        raise SystemExit('release checked-prefix selection changed: ' + text)
if not (checked_path.index('take_n($overflow_digits)') <
        checked_path.index('parse_digits_unchecked!') <
        checked_path.index('parse_1digit_checked!')):
    raise SystemExit('release checked-prefix order changed')
unchecked_path = macro_body(release, 'parse_digits_unchecked')
if 'parse_1digit_unchecked!' not in unchecked_path or '$no_multi_digit' not in unchecked_path:
    raise SystemExit('release no_multi_digit unchecked selection changed')
algorithm = macro_body(release, 'algorithm')
for anchor in ('parse_sign::<T, FORMAT>', 'iter.is_buffer_empty()',
               'T::overflow_digits(radix)', 'let cannot_overflow =',
               'parse_digits_unchecked!', 'parse_digits_checked!'):
    if anchor not in algorithm:
        raise SystemExit('release frontend selection changed: ' + anchor)

# Actual lexical-util Integer::overflow_digits body, with trait constants
# substituted by the explicit parameters of the safe frontend.
orig = balanced_body(util_num, 'fn overflow_digits(radix: u32) -> usize')
orig = orig.replace('mem::size_of::<Self>()', 'byte_width')
orig = orig.replace('Self::IS_SIGNED as usize', 'signed as usize')
fail_compare('overflow_digits', balanced_body(source,
    'pub fn overflow_digits(byte_width: usize, signed: bool, radix: u32)'), orig)

# Direct literal sign handling is the selected standard format behavior.
fail_compare('unsigned_start', balanced_body(source, 'pub fn unsigned_start('),
    "if !bytes.is_empty() && bytes[0] == b'+' { 1 } else { 0 }")
fail_compare('signed_start', balanced_body(source, 'pub fn signed_start('),
    "if bytes.is_empty() { return (false, 0); }"
    "if bytes[0] == b'+' { return (false, 1); }"
    "if bytes[0] == b'-' { return (true, 1); }"
    "(false, 0)")

# Transform the release's exact one-digit unchecked macro into the safe
# iterator/cursor outline. The format-invalid action differs by complete vs
# partial caller, and is checked separately for all four macro families.
unchecked = macro_body(release, 'parse_1digit_unchecked')
unchecked = unchecked.replace('let radix = NumberFormat::<FORMAT>::MANTISSA_RADIX;', '')
unchecked = unchecked.replace('$value', 'value').replace('$iter', 'iter')
unchecked = unchecked.replace('as_cast(radix)', 'radix as $ty')
unchecked = unchecked.replace('as_cast(digit)', 'digit as $ty')
unchecked = unchecked.replace('while let Some(&c) = iter.next() {',
                              'while let Some(&c) = iter.next() { cursor += 1;')
for macro, op, partial in (
    ('unsigned_front', 'wrapping_add', False),
    ('signed_path', '$op', False),
    ('unsigned_partial_front', 'wrapping_add', True),
    ('signed_partial_path', '$op', True),
):
    want = unchecked.replace('$add_op', op)
    want = re.sub(r'Some\(v\)\s*=>\s*v', 'Some(d)=>d', want)
    invalid = ('return Ok((value, cursor - 1))' if partial else
               'return Err(Error::InvalidDigit(cursor - 1))')
    want = want.replace('fmt_invalid_digit!(value, iter, c, $start_index, $invalid_digit, $is_end)', invalid)
    if macro != 'unsigned_front':
        want = want.replace(invalid + ',', invalid)
    want = 'let mut iter = bytes.iter();' + want + ('Ok((value,cursor))' if partial else 'Ok(value)')
    actual = balanced_body(source[source.index('macro_rules! '+macro):], 'pub fn $unchecked(')
    fail_compare(macro + ' unchecked scalar', actual, want)

# The explicit slice/cursor frontends are reviewed adaptations of algorithm!
# and parse_digits_checked!; compare their entire selected control flow. These
# literal templates make changes to sign, empty, prefix, checked continuation,
# and partial early return visible to review.
manual = {
 'unsigned_front': {
  'pub fn $front(': '$tail(bytes, unsigned_start(bytes), radix)',
  'pub fn $tail(': '''if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
   let digits = &bytes[cursor..];
   let count = overflow_digits($bytes, false, radix);
   if digits.len() <= count { return $unchecked(digits, 0, cursor, radix); }
   let value = $unchecked(&digits[..count], 0, cursor, radix)?;
   checked::$checked(&digits[count..], value, cursor + count, radix)''',
 },
 'signed_path': {
  'pub fn $tail(': '''if cursor==bytes.len(){return Err(Error::Empty(cursor));}
   let digits=&bytes[cursor..];
   let count=overflow_digits($bytes,true,radix);
   if digits.len()<=count{return $unchecked(digits,0,cursor,radix);}
   let value=$unchecked(&digits[..count],0,cursor,radix)?;
   checked::$checked(&digits[count..],value,cursor+count,radix)''',
 },
 'signed_front': {
  'pub fn $front(': '''let (negative,cursor)=signed_start(bytes);
   if negative{$negative(bytes,cursor,radix)}else{$positive(bytes,cursor,radix)}''',
 },
 'unsigned_partial_front': {
  'pub fn $tail(': '''if cursor==bytes.len(){return Err(Error::Empty(cursor));}
   let digits=&bytes[cursor..];
   let count=overflow_digits($bytes,false,radix);
   if digits.len()<=count{return $unchecked(digits,0,cursor,radix);}
   let (value,ended)=$unchecked(&digits[..count],0,cursor,radix)?;
   if ended<cursor+count{return Ok((value,ended));}
   checked::partial::$checked(&digits[count..],value,cursor+count,radix)''',
  'pub fn $front(': '$tail(bytes,unsigned_start(bytes),radix)',
 },
 'signed_partial_path': {
  'pub fn $tail(': '''if cursor==bytes.len(){return Err(Error::Empty(cursor));}
   let digits=&bytes[cursor..];
   let count=overflow_digits($bytes,true,radix);
   if digits.len()<=count{return $unchecked(digits,0,cursor,radix);}
   let (value,ended)=$unchecked(&digits[..count],0,cursor,radix)?;
   if ended<cursor+count{return Ok((value,ended));}
   checked::partial::$checked(&digits[count..],value,cursor+count,radix)''',
 },
 'signed_partial_front': {
  'pub fn $front(': '''let (negative,cursor)=signed_start(bytes);
   if negative{$negative(bytes,cursor,radix)}else{$positive(bytes,cursor,radix)}''',
 },
}
for macro, pieces in manual.items():
    section = source[source.index('macro_rules! '+macro):]
    for marker, want in pieces.items():
        fail_compare(macro + ' ' + marker, balanced_body(section, marker), want)

# All 24 public whole-input adaptations and their helper specializations are
# selected with the exact width, sign direction, and prefix byte count.
compact = re.sub(r'\s+', '', source)
widths = [('u8',1),('u16',2),('u32',4),('u64',8),('u128',16),('usize',8)]
for ty, width in widths:
    for mode in ('complete','partial'):
        name = 'unsigned_front' if mode == 'complete' else 'unsigned_partial_front'
        call = (f'{name}!({mode}_{ty},{mode}_{ty}_from_cursor,'
                f'unchecked_{ty}' + ('_partial' if mode == 'partial' else '') + ','
                f'checked_{ty}' + ('_partial' if mode == 'partial' else '') +
                f',{ty},{width});')
        if compact.count(call) != 1:
            raise SystemExit('missing or duplicate unsigned frontend: ' + call)
for ty, width in [('i8',1),('i16',2),('i32',4),('i64',8),('i128',16),('isize',8)]:
    for mode in ('complete','partial'):
        path = 'signed_path' if mode == 'complete' else 'signed_partial_path'
        front = 'signed_front' if mode == 'complete' else 'signed_partial_front'
        for direction, op in [('positive','wrapping_add'),('negative','wrapping_sub')]:
            name = f'{mode}_{ty}_{direction}_from_cursor'
            uncheck = f'unchecked_{ty}_{direction}' + ('_partial' if mode == 'partial' else '')
            checked = f'checked_{ty}_{direction}' + ('_partial' if mode == 'partial' else '')
            call = f'{path}!({name},{uncheck},{checked},{op},{ty},{width});'
            if compact.count(call) != 1:
                raise SystemExit('missing or duplicate signed path: ' + call)
        call = f'{front}!({mode}_{ty},{mode}_{ty}_positive_from_cursor,{mode}_{ty}_negative_from_cursor,{ty});'
        if compact.count(call) != 1:
            raise SystemExit('missing or duplicate signed frontend: ' + call)

# All selected dependency source files must exactly match the locked crate
# archive, including iterator/format/num bodies used for correspondence.
lock = tomllib.loads((FRONT / 'Cargo.lock').read_text())
util = next(p for p in lock['package'] if p['name'] == 'lexical-util')
archive = next((ROOT / '.work/cargo-home/registry/cache').glob('*/lexical-util-1.0.7.crate'))
if hashlib.sha256(archive.read_bytes()).hexdigest() != util['checksum']:
    raise SystemExit('lexical-util archive differs from front Cargo.lock checksum')
with tarfile.open(archive) as crate:
    for entry in crate.getmembers():
        if not entry.isfile() or not entry.name.startswith('lexical-util-1.0.7/src/'):
            continue
        rel = entry.name.removeprefix('lexical-util-1.0.7/')
        if (util_root / rel).read_bytes() != crate.extractfile(entry).read():
            raise SystemExit('selected lexical-util source differs from locked archive: ' + rel)

# The independent Astra pure specification is copied without modification.
for name in ('DigitSpecs.lean', 'GenericScalarSpecs.lean'):
    parser = ROOT / 'aeneas/profiles/parser/proofs' / name
    front = ROOT / 'aeneas/profiles/generic_front/proofs' / name
    if front.read_bytes() != parser.read_bytes():
        raise SystemExit('generic frontend pure spec differs from Astra parser copy: ' + name)
print('generic frontend release macro/state adaptations, 24 specializations, dependency and specs match pinned inputs')
