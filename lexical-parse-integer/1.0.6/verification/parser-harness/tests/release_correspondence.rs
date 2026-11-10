use lexical_parse_integer_parser_harness::{checked_u32, checked_i32_negative_from, checked_i32_positive_from, complete_u8, partial_u8};
use release::FromLexical;
use lexical_parse_integer_parser_harness::{complete_i8, partial_i8};

fn compare(bytes: &[u8]) {
    assert_eq!(complete_u8(bytes), u8::from_lexical(bytes), "complete {bytes:?}");
    assert_eq!(partial_u8(bytes), u8::from_lexical_partial(bytes), "partial {bytes:?}");
    assert_eq!(complete_i8(bytes), i8::from_lexical(bytes), "signed complete {bytes:?}");
    assert_eq!(partial_i8(bytes), i8::from_lexical_partial(bytes), "signed partial {bytes:?}");
    // Sign and empty policy are caller responsibilities, outside this loop.
    if bytes.is_empty() || bytes[0] == b'+' {
        return;
    }
    assert_eq!(checked_u32(bytes, 0), u32::from_lexical(bytes), "{bytes:?}");
    if bytes[0] != b'-' {
        assert_eq!(checked_i32_positive_from(bytes, 0, 0), i32::from_lexical(bytes), "{bytes:?}");
    }
    let mut negative = vec![b'-'];
    negative.extend_from_slice(bytes);
    assert_eq!(checked_i32_negative_from(bytes, 0, 1), i32::from_lexical(&negative), "{negative:?}");
}

#[test]
fn outlined_loop_agrees_with_release_on_unsigned_digit_body() {
    for text in ["", "+", "-", "+0", "++1", "-1", "127", "128", "-128", "-129", "-0", "-a1234", "-1a234", "-12a34", "255", "256", "+255", "+256", "25a", "2a5", "a25", "a12345", "1a2345", "+a12345", "+1a2345", "12a345", "+12a345", "000000000000000000000001", "999999999a"] {
        compare(text.as_bytes());
    }
    for text in ["0", "2147483647", "2147483648", "2147483649", "4294967295", "4294967296", "999999999999a", "00000000000000000000", "123a999999999"] {
        compare(text.as_bytes());
    }
    for a in 0..=255u8 {
        for b in 0..=255u8 {
            compare(&[a, b]);
        }
    }
    let mut state = 0x61235789abcdef01u64;
    for length in 1..=40 {
        for _ in 0..1000 {
            let bytes: Vec<u8> = (0..length).map(|_| {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                if state & 7 != 0 { b'0' + (state % 10) as u8 } else { state as u8 }
            }).collect();
            compare(&bytes);
        }
    }
}
