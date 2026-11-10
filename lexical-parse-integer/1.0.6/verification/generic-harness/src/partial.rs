//! Partial-mode adaptation of the release checked scalar macro.
use lexical_util::digit::char_to_digit_const;
use lexical_util::error::Error;

macro_rules! unsigned_partial {
    ($name:ident, $ty:ty) => {
        pub fn $name(bytes: &[u8], mut value: $ty, mut cursor: usize, radix: u32)
            -> Result<($ty, usize), Error>
        {
            let mut iter = bytes.iter();
            while let Some(&c) = iter.next() {
                cursor += 1;
                let digit = match char_to_digit_const(c, radix) {
                    Some(v) => v,
                    None => return Ok((value, cursor - 1)),
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
            Ok((value, cursor))
        }
    };
}

macro_rules! signed_partial {
    ($name:ident, $ty:ty, $operation:ident, $error:ident) => {
        pub fn $name(bytes: &[u8], mut value: $ty, mut cursor: usize, radix: u32)
            -> Result<($ty, usize), Error>
        {
            let mut iter = bytes.iter();
            while let Some(&c) = iter.next() {
                cursor += 1;
                let digit = match char_to_digit_const(c, radix) {
                    Some(v) => v,
                    None => return Ok((value, cursor - 1)),
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
            Ok((value, cursor))
        }
    };
}

unsigned_partial!(checked_u8_partial, u8);
unsigned_partial!(checked_u16_partial, u16);
unsigned_partial!(checked_u32_partial, u32);
unsigned_partial!(checked_u64_partial, u64);
unsigned_partial!(checked_u128_partial, u128);
unsigned_partial!(checked_usize_partial, usize);
signed_partial!(checked_i8_positive_partial, i8, checked_add, Overflow);
signed_partial!(checked_i8_negative_partial, i8, checked_sub, Underflow);
signed_partial!(checked_i16_positive_partial, i16, checked_add, Overflow);
signed_partial!(checked_i16_negative_partial, i16, checked_sub, Underflow);
signed_partial!(checked_i32_positive_partial, i32, checked_add, Overflow);
signed_partial!(checked_i32_negative_partial, i32, checked_sub, Underflow);
signed_partial!(checked_i64_positive_partial, i64, checked_add, Overflow);
signed_partial!(checked_i64_negative_partial, i64, checked_sub, Underflow);
signed_partial!(checked_i128_positive_partial, i128, checked_add, Overflow);
signed_partial!(checked_i128_negative_partial, i128, checked_sub, Underflow);
signed_partial!(checked_isize_positive_partial, isize, checked_add, Overflow);
signed_partial!(checked_isize_negative_partial, isize, checked_sub, Underflow);
