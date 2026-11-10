//! Concrete entry points into the unchanged release's block callers.

use lexical_parse_integer::algorithm::{try_parse_4digits, try_parse_8digits};
use lexical_util::format::STANDARD;
use lexical_util::iterator::{Bytes, Iter};

#[path = "../../harness/src/lib.rs"]
mod swar;

pub mod safe;

pub fn try4_u32(bytes: &[u8]) -> (Option<u32>, usize) {
    let mut byte = Bytes::<STANDARD>::new(bytes);
    let mut iter = byte.integer_iter();
    let value = try_parse_4digits::<u32, _, STANDARD>(&mut iter);
    (value, iter.cursor())
}

pub fn try8_u64(bytes: &[u8]) -> (Option<u64>, usize) {
    let mut byte = Bytes::<STANDARD>::new(bytes);
    let mut iter = byte.integer_iter();
    let value = try_parse_8digits::<u64, _, STANDARD>(&mut iter);
    (value, iter.cursor())
}

/// Reach a valid nonzero no-skip iterator cursor through its public `next`.
pub fn try4_u32_from(bytes: &[u8], cursor: usize) -> (Option<u32>, usize) {
    assert!(cursor <= bytes.len());
    let mut byte = Bytes::<STANDARD>::new(bytes);
    let mut iter = byte.integer_iter();
    for _ in 0..cursor {
        iter.next();
    }
    let value = try_parse_4digits::<u32, _, STANDARD>(&mut iter);
    (value, iter.cursor())
}

pub fn try8_u64_from(bytes: &[u8], cursor: usize) -> (Option<u64>, usize) {
    assert!(cursor <= bytes.len());
    let mut byte = Bytes::<STANDARD>::new(bytes);
    let mut iter = byte.integer_iter();
    for _ in 0..cursor {
        iter.next();
    }
    let value = try_parse_8digits::<u64, _, STANDARD>(&mut iter);
    (value, iter.cursor())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn release_caller_observations() {
        assert_eq!(try4_u32(b"1234!"), (Some(1234), 4));
        assert_eq!(try4_u32(b"12?4"), (None, 0));
        assert_eq!(try4_u32(b"123"), (None, 0));
        assert_eq!(try8_u64(b"12345678!"), (Some(12345678), 8));
        assert_eq!(try8_u64(b"1234?678"), (None, 0));
        assert_eq!(try8_u64(b"1234567"), (None, 0));
    }

    #[test]
    fn safe_adapter_matches_release_at_zero() {
        for position in 0..4 {
            for byte in 0..=255u8 {
                let mut input = *b"1234";
                input[position] = byte;
                assert_eq!(safe::try4(&input, 0), try4_u32(&input), "four: {input:?}");
            }
        }
        for position in 0..8 {
            for byte in 0..=255u8 {
                let mut input = *b"12345678";
                input[position] = byte;
                assert_eq!(safe::try8(&input, 0), try8_u64(&input), "eight: {input:?}");
            }
        }
        for n in 0..8 {
            assert_eq!(safe::try4(&b"12345678"[..n], 0), try4_u32(&b"12345678"[..n]));
            assert_eq!(safe::try8(&b"12345678"[..n], 0), try8_u64(&b"12345678"[..n]));
        }
    }

    #[test]
    fn safe_adapter_matches_nonzero_iterator_cursor() {
        for (input, cursor) in [
            (&b"x1234!"[..], 1),
            (&b"xy12?4"[..], 2),
            (&b"xy123"[..], 2),
            (&b"xyz12345678!"[..], 3),
            (&b"xyz1234?678"[..], 3),
            (&b"xyz1234567"[..], 3),
        ] {
            assert_eq!(
                safe::try4(&input[cursor..], cursor),
                try4_u32_from(input, cursor),
                "four: {input:?}, cursor={cursor}"
            );
            assert_eq!(
                safe::try8(&input[cursor..], cursor),
                try8_u64_from(input, cursor),
                "eight: {input:?}, cursor={cursor}"
            );
        }
    }
}
