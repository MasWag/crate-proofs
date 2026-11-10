use lexical_parse_integer::{FromLexical, FromLexicalWithOptions, Options};
use lexical_util::error::Error;
#[cfg(feature = "format")]
use lexical_util::format::NumberFormatBuilder;
use lexical_util::format::STANDARD;

#[test]
fn decimal_boundaries() {
    assert_eq!(u8::from_lexical_partial(b"255!"), Ok((255, 3)));
    assert_eq!(u8::from_lexical_partial(b"256!"), Err(Error::Overflow(2)));
    assert_eq!(i8::from_lexical_partial(b"-128!"), Ok((-128, 4)));
    assert_eq!(i8::from_lexical_partial(b"-129!"), Err(Error::Underflow(3)));
    assert_eq!(i8::from_lexical_partial(b"127!"), Ok((127, 3)));
    assert_eq!(i8::from_lexical_partial(b"128!"), Err(Error::Overflow(2)));
}

#[test]
fn decimal_matches_rust_integer_parsing_with_both_digit_paths() {
    for no_multi_digit in [true, false] {
        let options = Options::builder()
            .no_multi_digit(no_multi_digit)
            .build_strict();
        for n in 0..=300u16 {
            let digits = n.to_string();
            let expected = digits.parse::<u8>();
            let complete = u8::from_lexical_with_options::<STANDARD>(digits.as_bytes(), &options);
            let mut terminated = digits.clone();
            terminated.push('!');
            let partial =
                u8::from_lexical_partial_with_options::<STANDARD>(terminated.as_bytes(), &options);
            match expected {
                Ok(value) => {
                    assert_eq!(
                        complete,
                        Ok(value),
                        "u8 {digits}, no_multi_digit={no_multi_digit}"
                    );
                    assert_eq!(
                        partial,
                        Ok((value, digits.len())),
                        "u8 partial {digits}, no_multi_digit={no_multi_digit}"
                    );
                }
                Err(_) => {
                    assert!(
                        complete.is_err(),
                        "u8 {digits}, no_multi_digit={no_multi_digit}"
                    );
                    assert!(
                        partial.is_err(),
                        "u8 partial {digits}, no_multi_digit={no_multi_digit}"
                    );
                }
            }
        }
        for n in -140..=140i16 {
            let digits = n.to_string();
            let expected = digits.parse::<i8>();
            let complete = i8::from_lexical_with_options::<STANDARD>(digits.as_bytes(), &options);
            let mut terminated = digits.clone();
            terminated.push('!');
            let partial =
                i8::from_lexical_partial_with_options::<STANDARD>(terminated.as_bytes(), &options);
            match expected {
                Ok(value) => {
                    assert_eq!(
                        complete,
                        Ok(value),
                        "i8 {digits}, no_multi_digit={no_multi_digit}"
                    );
                    assert_eq!(
                        partial,
                        Ok((value, digits.len())),
                        "i8 partial {digits}, no_multi_digit={no_multi_digit}"
                    );
                }
                Err(_) => {
                    assert!(
                        complete.is_err(),
                        "i8 {digits}, no_multi_digit={no_multi_digit}"
                    );
                    assert!(
                        partial.is_err(),
                        "i8 partial {digits}, no_multi_digit={no_multi_digit}"
                    );
                }
            }
        }
        for digits in [
            "0",
            "340282366920938463463374607431768211455",
            "340282366920938463463374607431768211456",
        ] {
            assert_eq!(
                u128::from_lexical_with_options::<STANDARD>(digits.as_bytes(), &options).ok(),
                digits.parse::<u128>().ok(),
                "u128 {digits}, no_multi_digit={no_multi_digit}"
            );
        }
        for digits in [
            "-170141183460469231731687303715884105728",
            "-170141183460469231731687303715884105729",
            "170141183460469231731687303715884105727",
            "170141183460469231731687303715884105728",
        ] {
            assert_eq!(
                i128::from_lexical_with_options::<STANDARD>(digits.as_bytes(), &options).ok(),
                digits.parse::<i128>().ok(),
                "i128 {digits}, no_multi_digit={no_multi_digit}"
            );
        }
    }
}

#[test]
#[ignore = "release 1.0.6 regression reproduction"]
#[cfg(feature = "format")]
fn no_leading_zero_partial_unsigned_consumes_single_zero() {
    const FORMAT: u128 = NumberFormatBuilder::new()
        .no_integer_leading_zeros(true)
        .build_strict();
    let options = Options::new();
    assert_eq!(
        u8::from_lexical_partial_with_options::<FORMAT>(b"0", &options),
        Ok((0, 1))
    );
}

#[test]
#[ignore = "release 1.0.6 regression reproduction"]
#[cfg(feature = "format")]
fn no_leading_zero_partial_signed_consumes_single_zero() {
    const FORMAT: u128 = NumberFormatBuilder::new()
        .no_integer_leading_zeros(true)
        .build_strict();
    let options = Options::new();
    assert_eq!(
        i8::from_lexical_partial_with_options::<FORMAT>(b"-0", &options),
        Ok((0, 2))
    );
}

#[test]
#[cfg(feature = "format")]
fn no_leading_zero_controls() {
    const FORMAT: u128 = NumberFormatBuilder::new()
        .no_integer_leading_zeros(true)
        .build_strict();
    let options = Options::new();
    assert_eq!(
        u8::from_lexical_with_options::<FORMAT>(b"0", &options),
        Ok(0)
    );
    assert_eq!(
        u8::from_lexical_partial_with_options::<FORMAT>(b"0!", &options),
        Ok((0, 1))
    );
    assert_eq!(
        u8::from_lexical_with_options::<FORMAT>(b"01", &options),
        Err(Error::InvalidLeadingZeros(0))
    );
}

#[test]
#[ignore = "release 1.0.6 regression reproduction"]
#[cfg(feature = "format")]
fn base_suffix_partial_does_not_consume_other_byte() {
    use core::num::NonZeroU8;
    const FORMAT: u128 = NumberFormatBuilder::new()
        .base_suffix(NonZeroU8::new(b'h'))
        .build_strict();
    let options = Options::new();
    assert_eq!(
        u8::from_lexical_partial_with_options::<FORMAT>(b"12?x", &options),
        Ok((12, 2))
    );
}

#[test]
#[ignore = "release 1.0.6 regression reproduction"]
#[cfg(feature = "format")]
fn base_suffix_complete_reports_first_invalid_byte() {
    use core::num::NonZeroU8;
    const FORMAT: u128 = NumberFormatBuilder::new()
        .base_suffix(NonZeroU8::new(b'h'))
        .build_strict();
    let options = Options::new();
    assert_eq!(
        u8::from_lexical_with_options::<FORMAT>(b"12?x", &options),
        Err(Error::InvalidDigit(2))
    );
}

#[test]
#[cfg(feature = "format")]
fn base_suffix_controls() {
    use core::num::NonZeroU8;
    const FORMAT: u128 = NumberFormatBuilder::new()
        .base_suffix(NonZeroU8::new(b'h'))
        .build_strict();
    let options = Options::new();
    assert_eq!(
        u8::from_lexical_partial_with_options::<FORMAT>(b"12?", &options),
        Ok((12, 2))
    );
    assert_eq!(
        u8::from_lexical_partial_with_options::<FORMAT>(b"12h?", &options),
        Ok((12, 3))
    );
}

#[test]
fn empty_prefix_observation() {
    eprintln!("? => {:?}", u8::from_lexical_partial(b"?"));
    eprintln!("+? => {:?}", u8::from_lexical_partial(b"+?"));
}
