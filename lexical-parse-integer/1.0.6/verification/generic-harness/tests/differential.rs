use lexical_parse_integer_generic_harness as outline;
use release::{format, FromLexicalWithOptions, NumberFormatBuilder, Options};

const OPTIONS: Options = Options::builder().no_multi_digit(true).build_strict();
const BINARY: u128 = NumberFormatBuilder::from_radix(2);
const HEX: u128 = NumberFormatBuilder::from_radix(16);

macro_rules! unsigned_cases {
    ($ty:ty, $name:ident, $format:expr, $radix:expr, $cases:expr) => {
        for bytes in $cases {
            let expected = <$ty>::from_lexical_with_options::<$format>(bytes, &OPTIONS);
            let actual = outline::$name(bytes, 0, 0, $radix);
            assert_eq!(actual, expected, "{} {:?}", stringify!($ty), bytes);
        }
    };
}

macro_rules! signed_cases {
    ($ty:ty, $positive:ident, $negative:ident, $format:expr, $radix:expr, $cases:expr) => {
        for bytes in $cases {
            let expected = <$ty>::from_lexical_with_options::<$format>(bytes, &OPTIONS);
            let actual = if bytes.first() == Some(&b'-') {
                outline::$negative(&bytes[1..], 0, 1, $radix)
            } else {
                outline::$positive(bytes, 0, 0, $radix)
            };
            assert_eq!(actual, expected, "{} {:?}", stringify!($ty), bytes);
        }
    };
}

#[test]
fn complete_decimal_matches_release_selected_widths() {
    let cases: &[&[u8]] = &[b"0", b"123", b"9999999999999999999999999999999999999999999999", b"12?34"];
    unsigned_cases!(u8, checked_u8, { format::STANDARD }, 10, cases);
    unsigned_cases!(u16, checked_u16, { format::STANDARD }, 10, cases);
    unsigned_cases!(u32, checked_u32, { format::STANDARD }, 10, cases);
    unsigned_cases!(u64, checked_u64, { format::STANDARD }, 10, cases);
    unsigned_cases!(u128, checked_u128, { format::STANDARD }, 10, cases);
    unsigned_cases!(usize, checked_usize, { format::STANDARD }, 10, cases);
    let signed: &[&[u8]] = &[b"0", b"127", b"-128", b"9999999999999999999999999999999999999999999999", b"-9999999999999999999999999999999999999999999999", b"12?34", b"-12?34"];
    signed_cases!(i8, checked_i8_positive, checked_i8_negative, { format::STANDARD }, 10, signed);
    signed_cases!(i16, checked_i16_positive, checked_i16_negative, { format::STANDARD }, 10, signed);
    signed_cases!(i32, checked_i32_positive, checked_i32_negative, { format::STANDARD }, 10, signed);
    signed_cases!(i64, checked_i64_positive, checked_i64_negative, { format::STANDARD }, 10, signed);
    signed_cases!(i128, checked_i128_positive, checked_i128_negative, { format::STANDARD }, 10, signed);
    signed_cases!(isize, checked_isize_positive, checked_isize_negative, { format::STANDARD }, 10, signed);
}

#[test]
fn complete_binary_hex_matches_release() {
    let binary: &[&[u8]] = &[b"101101", b"111111111111111111111111111111111", b"10?11"];
    unsigned_cases!(u8, checked_u8, { BINARY }, 2, binary);
    unsigned_cases!(u128, checked_u128, { BINARY }, 2, binary);
    let hex: &[&[u8]] = &[b"7F", b"80", b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", b"aZ"];
    signed_cases!(i8, checked_i8_positive, checked_i8_negative, { HEX }, 16, hex);
    unsigned_cases!(u128, checked_u128, { HEX }, 16, hex);
}

macro_rules! unsigned_partial_cases {
    ($ty:ty, $name:ident, $format:expr, $radix:expr, $cases:expr) => {
        for bytes in $cases {
            let expected = <$ty>::from_lexical_partial_with_options::<$format>(bytes, &OPTIONS);
            let actual = outline::partial::$name(bytes, 0, 0, $radix);
            assert_eq!(actual, expected, "partial {} {:?}", stringify!($ty), bytes);
        }
    };
}

macro_rules! signed_partial_cases {
    ($ty:ty, $positive:ident, $negative:ident, $format:expr, $radix:expr, $cases:expr) => {
        for bytes in $cases {
            let expected = <$ty>::from_lexical_partial_with_options::<$format>(bytes, &OPTIONS);
            let actual = if bytes.first() == Some(&b'-') {
                outline::partial::$negative(&bytes[1..], 0, 1, $radix)
            } else {
                outline::partial::$positive(bytes, 0, 0, $radix)
            };
            assert_eq!(actual, expected, "partial {} {:?}", stringify!($ty), bytes);
        }
    };
}

#[test]
fn partial_decimal_matches_release_selected_widths() {
    let unsigned: &[&[u8]] = &[b"0", b"123?45", b"9999999999999999999999999999999999999999999999", b"1?2"];
    unsigned_partial_cases!(u8, checked_u8_partial, { format::STANDARD }, 10, unsigned);
    unsigned_partial_cases!(u16, checked_u16_partial, { format::STANDARD }, 10, unsigned);
    unsigned_partial_cases!(u32, checked_u32_partial, { format::STANDARD }, 10, unsigned);
    unsigned_partial_cases!(u64, checked_u64_partial, { format::STANDARD }, 10, unsigned);
    unsigned_partial_cases!(u128, checked_u128_partial, { format::STANDARD }, 10, unsigned);
    unsigned_partial_cases!(usize, checked_usize_partial, { format::STANDARD }, 10, unsigned);
    let signed: &[&[u8]] = &[b"0", b"127?45", b"-128?45", b"9999999999999999999999999999999999999999999999", b"-9999999999999999999999999999999999999999999999", b"-12?34", b"1?2"];
    signed_partial_cases!(i8, checked_i8_positive_partial, checked_i8_negative_partial, { format::STANDARD }, 10, signed);
    signed_partial_cases!(i16, checked_i16_positive_partial, checked_i16_negative_partial, { format::STANDARD }, 10, signed);
    signed_partial_cases!(i32, checked_i32_positive_partial, checked_i32_negative_partial, { format::STANDARD }, 10, signed);
    signed_partial_cases!(i64, checked_i64_positive_partial, checked_i64_negative_partial, { format::STANDARD }, 10, signed);
    signed_partial_cases!(i128, checked_i128_positive_partial, checked_i128_negative_partial, { format::STANDARD }, 10, signed);
    signed_partial_cases!(isize, checked_isize_positive_partial, checked_isize_negative_partial, { format::STANDARD }, 10, signed);
}

#[test]
fn partial_binary_hex_matches_release() {
    let binary: &[&[u8]] = &[b"101101?", b"111111111111111111111111111111111", b"10?11"];
    unsigned_partial_cases!(u8, checked_u8_partial, { BINARY }, 2, binary);
    unsigned_partial_cases!(u128, checked_u128_partial, { BINARY }, 2, binary);
    let hex: &[&[u8]] = &[b"7F?", b"80?", b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", b"aZ"];
    signed_partial_cases!(i8, checked_i8_positive_partial, checked_i8_negative_partial, { HEX }, 16, hex);
    unsigned_partial_cases!(u128, checked_u128_partial, { HEX }, 16, hex);
}
