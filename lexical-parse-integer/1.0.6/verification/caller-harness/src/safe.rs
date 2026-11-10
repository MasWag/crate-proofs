//! A scoped safe-read adaptation of the release block callers.
//! `bytes` represents the iterator's remaining contiguous slice.

use super::swar;

pub fn try4(bytes: &[u8], cursor: usize) -> (Option<u32>, usize) {
    if bytes.len() < 4 {
        return (None, cursor);
    }
    let word = (bytes[0] as u32)
        + ((bytes[1] as u32) << 8)
        + ((bytes[2] as u32) << 16)
        + ((bytes[3] as u32) << 24);
    if swar::is_4digits(word) {
        (Some(swar::parse_4digits(word)), cursor + 4)
    } else {
        (None, cursor)
    }
}

pub fn try8(bytes: &[u8], cursor: usize) -> (Option<u64>, usize) {
    if bytes.len() < 8 {
        return (None, cursor);
    }
    let word = (bytes[0] as u64)
        + ((bytes[1] as u64) << 8)
        + ((bytes[2] as u64) << 16)
        + ((bytes[3] as u64) << 24)
        + ((bytes[4] as u64) << 32)
        + ((bytes[5] as u64) << 40)
        + ((bytes[6] as u64) << 48)
        + ((bytes[7] as u64) << 56);
    if swar::is_8digits(word) {
        (Some(swar::parse_8digits(word)), cursor + 8)
    } else {
        (None, cursor)
    }
}
