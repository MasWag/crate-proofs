//! Outlined scalar checked-loop probe. This is not the complete parser.
//! Arithmetic/control order follows algorithm.rs::parse_1digit_checked.
use lexical_util::digit::char_to_digit_const;
pub use lexical_util::error::Error;

pub fn checked_u32(bytes: &[u8], value: u32) -> Result<u32, Error> {
    checked_u32_from(bytes, value, 0)
}

pub fn checked_u32_from(bytes: &[u8], mut value: u32, mut cursor: usize) -> Result<u32, Error> {
    let mut iter = bytes.iter();
    let radix = 10;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        let combined = match value.checked_mul(radix) {
            Some(x) => x.checked_add(digit),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Overflow(cursor - 1)),
        };
    }
    Ok(value)
}

/// Negative signed specialization of the same checked scalar macro.
pub fn checked_i32_negative_from(bytes: &[u8], mut value: i32, mut cursor: usize) -> Result<i32, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        let combined = match value.checked_mul(radix as i32) {
            Some(x) => x.checked_sub(digit as i32),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Underflow(cursor - 1)),
        };
    }
    Ok(value)
}

/// Positive signed specialization of the same checked scalar macro.
pub fn checked_i32_positive_from(bytes: &[u8], mut value: i32, mut cursor: usize) -> Result<i32, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        let combined = match value.checked_mul(radix as i32) {
            Some(x) => x.checked_add(digit as i32),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Overflow(cursor - 1)),
        };
    }
    Ok(value)
}

pub fn checked_u8_from(bytes: &[u8], mut value: u8, mut cursor: usize) -> Result<u8, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        let combined = match value.checked_mul(radix as u8) {
            Some(x) => x.checked_add(digit as u8),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Overflow(cursor - 1)),
        };
    }
    Ok(value)
}

pub fn unchecked_u8_from(bytes: &[u8], mut value: u8, mut cursor: usize) -> Result<u8, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        value = value.wrapping_mul(radix as u8).wrapping_add(digit as u8);
    }
    Ok(value)
}

/// Default-format u8 complete parser, with the release's two-digit unchecked
/// prefix and checked remainder. Slice cuts expose the no-skip iterator state.
pub fn complete_u8(bytes: &[u8]) -> Result<u8, Error> {
    let cursor = if !bytes.is_empty() && bytes[0] == b'+' { 1 } else { 0 };
    complete_u8_from_cursor(bytes, cursor)
}


pub fn complete_u8_from_cursor(bytes: &[u8], cursor: usize) -> Result<u8, Error> {
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 2 {
        return unchecked_u8_from(digits, 0, cursor);
    }
    let value = unchecked_u8_from(&digits[..2], 0, cursor)?;
    checked_u8_from(&digits[2..], value, cursor + 2)
}


pub fn checked_u8_partial_from(bytes: &[u8], mut value: u8, mut cursor: usize) -> Result<(u8, usize), Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Ok((value, cursor - 1)),
        };
        let combined = match value.checked_mul(radix as u8) {
            Some(x) => x.checked_add(digit as u8),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Overflow(cursor - 1)),
        };
    }
    Ok((value, cursor))
}

pub fn unchecked_u8_partial_from(bytes: &[u8], mut value: u8, mut cursor: usize) -> Result<(u8, usize), Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Ok((value, cursor - 1)),
        };
        value = value.wrapping_mul(radix as u8).wrapping_add(digit as u8);
    }
    Ok((value, cursor))
}

pub fn partial_u8(bytes: &[u8]) -> Result<(u8, usize), Error> {
    let cursor = if !bytes.is_empty() && bytes[0] == b'+' { 1 } else { 0 };
    partial_u8_from_cursor(bytes, cursor)
}

pub fn partial_u8_from_cursor(bytes: &[u8], cursor: usize) -> Result<(u8, usize), Error> {
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 2 {
        return unchecked_u8_partial_from(digits, 0, cursor);
    }
    let (value, end) = unchecked_u8_partial_from(&digits[..2], 0, cursor)?;
    if end < cursor + 2 { return Ok((value, end)); }
    checked_u8_partial_from(&digits[2..], value, cursor + 2)
}


pub fn checked_i8_negative_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<i8, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        let combined = match value.checked_mul(radix as i8) {
            Some(x) => x.checked_sub(digit as i8),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Underflow(cursor - 1)),
        };
    }
    Ok(value)
}

pub fn unchecked_i8_negative_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<i8, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        value = value.wrapping_mul(radix as i8).wrapping_sub(digit as i8);
    }
    Ok(value)
}

pub fn checked_i8_negative_partial_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<(i8, usize), Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Ok((value, cursor - 1)),
        };
        let combined = match value.checked_mul(radix as i8) {
            Some(x) => x.checked_sub(digit as i8),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Underflow(cursor - 1)),
        };
    }
    Ok((value, cursor))
}

pub fn unchecked_i8_negative_partial_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<(i8, usize), Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Ok((value, cursor - 1)),
        };
        value = value.wrapping_mul(radix as i8).wrapping_sub(digit as i8);
    }
    Ok((value, cursor))
}

pub fn checked_i8_positive_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<i8, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        let combined = match value.checked_mul(radix as i8) {
            Some(x) => x.checked_add(digit as i8),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Overflow(cursor - 1)),
        };
    }
    Ok(value)
}

pub fn unchecked_i8_positive_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<i8, Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Err(Error::InvalidDigit(cursor - 1)),
        };
        value = value.wrapping_mul(radix as i8).wrapping_add(digit as i8);
    }
    Ok(value)
}

pub fn checked_i8_positive_partial_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<(i8, usize), Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Ok((value, cursor - 1)),
        };
        let combined = match value.checked_mul(radix as i8) {
            Some(x) => x.checked_add(digit as i8),
            None => None,
        };
        value = match combined {
            Some(value) => value,
            None => return Err(Error::Overflow(cursor - 1)),
        };
    }
    Ok((value, cursor))
}

pub fn unchecked_i8_positive_partial_from(bytes: &[u8], mut value: i8, mut cursor: usize) -> Result<(i8, usize), Error> {
    let mut iter = bytes.iter();
    let radix = 10u32;
    while let Some(&c) = iter.next() {
        cursor += 1;
        let digit = match char_to_digit_const(c, radix) {
            Some(v) => v,
            None => return Ok((value, cursor - 1)),
        };
        value = value.wrapping_mul(radix as i8).wrapping_add(digit as i8);
    }
    Ok((value, cursor))
}

pub fn sign_i8(bytes: &[u8]) -> (bool, usize) {
    if bytes.is_empty() { return (false, 0); }
    if bytes[0] == b'+' { return (false, 1); }
    if bytes[0] == b'-' { return (true, 1); }
    (false, 0)
}

pub fn complete_i8(bytes: &[u8]) -> Result<i8, Error> {
    let (negative, cursor) = sign_i8(bytes);
    if negative { complete_i8_negative_from_cursor(bytes, cursor) }
    else { complete_i8_positive_from_cursor(bytes, cursor) }
}

pub fn partial_i8(bytes: &[u8]) -> Result<(i8, usize), Error> {
    let (negative, cursor) = sign_i8(bytes);
    if negative { partial_i8_negative_from_cursor(bytes, cursor) }
    else { partial_i8_positive_from_cursor(bytes, cursor) }
}

pub fn complete_i8_negative_from_cursor(bytes: &[u8], cursor: usize) -> Result<i8, Error> {
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_negative_from(digits, 0, cursor); }
    let value = unchecked_i8_negative_from(&digits[..1], 0, cursor)?;
    checked_i8_negative_from(&digits[1..], value, cursor + 1)
}

pub fn complete_i8_positive_from_cursor(bytes: &[u8], cursor: usize) -> Result<i8, Error> {
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_positive_from(digits, 0, cursor); }
    let value = unchecked_i8_positive_from(&digits[..1], 0, cursor)?;
    checked_i8_positive_from(&digits[1..], value, cursor + 1)
}

pub fn partial_i8_negative_from_cursor(bytes: &[u8], cursor: usize) -> Result<(i8, usize), Error> {
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_negative_partial_from(digits, 0, cursor); }
    let (value, end) = unchecked_i8_negative_partial_from(&digits[..1], 0, cursor)?;
    if end < cursor + 1 { return Ok((value, end)); }
    checked_i8_negative_partial_from(&digits[1..], value, cursor + 1)
}

pub fn partial_i8_positive_from_cursor(bytes: &[u8], cursor: usize) -> Result<(i8, usize), Error> {
    if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
    let digits = &bytes[cursor..];
    if digits.len() <= 1 { return unchecked_i8_positive_partial_from(digits, 0, cursor); }
    let (value, end) = unchecked_i8_positive_partial_from(&digits[..1], 0, cursor)?;
    if end < cursor + 1 { return Ok((value, end)); }
    checked_i8_positive_partial_from(&digits[1..], value, cursor + 1)
}
