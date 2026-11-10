//! Scalar no-multi-digit release macro outline over primitive widths.
//! This module preserves digit-before-arithmetic and checked mul/add order.
use lexical_util::digit::char_to_digit_const;
pub use lexical_util::error::Error;

macro_rules! unsigned_checked {
    ($name:ident, $ty:ty) => {
        pub fn $name(bytes: &[u8], mut value: $ty, mut cursor: usize, radix: u32)
            -> Result<$ty, Error>
        {
            let mut iter = bytes.iter();
            while let Some(&c) = iter.next() {
                cursor += 1;
                let digit = match char_to_digit_const(c, radix) {
                    Some(v) => v,
                    None => return Err(Error::InvalidDigit(cursor - 1)),
                };
                let combined = match value.checked_mul(radix as $ty) {
                    Some(x) => x.checked_add(digit as $ty),
                    None => None,
                };
                value = match combined {
                    Some(value) => value,
                    None => return Err(Error::Overflow(cursor - 1)),
                };
            }
            Ok(value)
        }
    };
}

macro_rules! signed_checked {
    ($name:ident, $ty:ty, $operation:ident, $error:ident) => {
        pub fn $name(bytes: &[u8], mut value: $ty, mut cursor: usize, radix: u32)
            -> Result<$ty, Error>
        {
            let mut iter = bytes.iter();
            while let Some(&c) = iter.next() {
                cursor += 1;
                let digit = match char_to_digit_const(c, radix) {
                    Some(v) => v,
                    None => return Err(Error::InvalidDigit(cursor - 1)),
                };
                let combined = match value.checked_mul(radix as $ty) {
                    Some(x) => x.$operation(digit as $ty),
                    None => None,
                };
                value = match combined {
                    Some(value) => value,
                    None => return Err(Error::$error(cursor - 1)),
                };
            }
            Ok(value)
        }
    };
}

unsigned_checked!(checked_u8, u8);
unsigned_checked!(checked_u16, u16);
unsigned_checked!(checked_u32, u32);
unsigned_checked!(checked_u64, u64);
unsigned_checked!(checked_u128, u128);
unsigned_checked!(checked_usize, usize);
signed_checked!(checked_i8_positive, i8, checked_add, Overflow);
signed_checked!(checked_i8_negative, i8, checked_sub, Underflow);
signed_checked!(checked_i16_positive, i16, checked_add, Overflow);
signed_checked!(checked_i16_negative, i16, checked_sub, Underflow);
signed_checked!(checked_i32_positive, i32, checked_add, Overflow);
signed_checked!(checked_i32_negative, i32, checked_sub, Underflow);
signed_checked!(checked_i64_positive, i64, checked_add, Overflow);
signed_checked!(checked_i64_negative, i64, checked_sub, Underflow);
signed_checked!(checked_i128_positive, i128, checked_add, Overflow);
signed_checked!(checked_i128_negative, i128, checked_sub, Underflow);
signed_checked!(checked_isize_positive, isize, checked_add, Overflow);
signed_checked!(checked_isize_negative, isize, checked_sub, Underflow);

pub mod partial;
