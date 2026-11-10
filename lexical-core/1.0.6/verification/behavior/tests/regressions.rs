use core::num::NonZeroU8;
use lexical_core::{Error, NumberFormatBuilder, ParseIntegerOptions};

const NO_LEADING_ZEROS: u128 = NumberFormatBuilder::new()
    .no_integer_leading_zeros(true)
    .build_strict();
const SUFFIX: u128 = NumberFormatBuilder::new()
    .base_suffix(NonZeroU8::new(b'h'))
    .build_strict();

#[test]
fn controls() {
    let options = ParseIntegerOptions::new();
    assert_eq!(lexical_core::parse_partial::<u8>(b"0"), Ok((0, 1)));
    assert_eq!(lexical_core::parse_with_options::<u8, NO_LEADING_ZEROS>(b"0", &options), Ok(0));
    assert_eq!(lexical_core::parse_partial_with_options::<u8, NO_LEADING_ZEROS>(b"0!", &options), Ok((0, 1)));
    assert_eq!(lexical_core::parse_with_options::<u8, NO_LEADING_ZEROS>(b"01", &options), Err(Error::InvalidLeadingZeros(0)));
    assert_eq!(lexical_core::parse_partial_with_options::<u8, SUFFIX>(b"12?", &options), Ok((12, 2)));
    assert_eq!(lexical_core::parse_partial_with_options::<u8, SUFFIX>(b"12h?", &options), Ok((12, 3)));
}

#[test]
#[ignore = "LC-001: release returns Ok((0, 0))"]
fn single_zero_consumes_one_byte() {
    let options = ParseIntegerOptions::new();
    let result = lexical_core::parse_partial_with_options::<u8, NO_LEADING_ZEROS>(b"0", &options);
    assert_eq!(result, Ok((0, 1)));
}

#[test]
#[ignore = "LC-001: release returns Ok((0, 1))"]
fn signed_zero_consumes_sign_and_zero() {
    let options = ParseIntegerOptions::new();
    let result = lexical_core::parse_partial_with_options::<i8, NO_LEADING_ZEROS>(b"-0", &options);
    assert_eq!(result, Ok((0, 2)));
}

#[test]
#[ignore = "LC-002: release returns Ok((12, 3))"]
fn unrelated_byte_is_not_a_suffix() {
    let options = ParseIntegerOptions::new();
    let result = lexical_core::parse_partial_with_options::<u8, SUFFIX>(b"12?x", &options);
    assert_eq!(result, Ok((12, 2)));
}

#[test]
#[ignore = "LC-002: release returns InvalidDigit(3)"]
fn complete_parse_reports_first_invalid_byte() {
    let options = ParseIntegerOptions::new();
    let result = lexical_core::parse_with_options::<u8, SUFFIX>(b"12?x", &options);
    assert_eq!(result, Err(Error::InvalidDigit(2)));
}
