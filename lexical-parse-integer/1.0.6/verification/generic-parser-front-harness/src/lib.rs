//! Standard syntax, no_multi_digit=true frontend adaptation.
//! Safe slice/cursor representation; preserves the release unchecked-prefix
//! selection before checked scanning. Source equivalence is reviewed separately.
use lexical_util::{digit::char_to_digit_const, error::Error};

pub fn overflow_digits(byte_width: usize, signed: bool, radix: u32) -> usize {
    if radix <= 16 { byte_width * 2 - signed as usize } else { byte_width }
}

pub fn unsigned_start(bytes: &[u8]) -> usize {
 if !bytes.is_empty() && bytes[0] == b'+' { 1 } else { 0 }
}

macro_rules! unsigned_front {
 ($front:ident, $tail:ident, $unchecked:ident, $checked:ident, $ty:ty, $bytes:expr) => {
  pub fn $unchecked(bytes: &[u8], mut value: $ty, mut cursor: usize, radix: u32) -> Result<$ty, Error> {
   let mut iter = bytes.iter();
   while let Some(&c) = iter.next() {
    cursor += 1;
    let digit = match char_to_digit_const(c, radix) {
     Some(d) => d, None => return Err(Error::InvalidDigit(cursor - 1)),
    };
    value = value.wrapping_mul(radix as $ty).wrapping_add(digit as $ty);
   }
   Ok(value)
  }
  pub fn $front(bytes: &[u8], radix: u32) -> Result<$ty, Error> {
   $tail(bytes, unsigned_start(bytes), radix)
  }
  pub fn $tail(bytes: &[u8], cursor: usize, radix: u32) -> Result<$ty, Error> {
   if cursor == bytes.len() { return Err(Error::Empty(cursor)); }
   let digits = &bytes[cursor..];
   let count = overflow_digits($bytes, false, radix);
   if digits.len() <= count { return $unchecked(digits, 0, cursor, radix); }
   let value = $unchecked(&digits[..count], 0, cursor, radix)?;
   checked::$checked(&digits[count..], value, cursor + count, radix)
  }
 };
}
unsigned_front!(complete_u8, complete_u8_from_cursor, unchecked_u8, checked_u8, u8, 1);
unsigned_front!(complete_u16, complete_u16_from_cursor, unchecked_u16, checked_u16, u16, 2);
unsigned_front!(complete_u32, complete_u32_from_cursor, unchecked_u32, checked_u32, u32, 4);
unsigned_front!(complete_u64, complete_u64_from_cursor, unchecked_u64, checked_u64, u64, 8);
unsigned_front!(complete_u128, complete_u128_from_cursor, unchecked_u128, checked_u128, u128, 16);
unsigned_front!(complete_usize, complete_usize_from_cursor, unchecked_usize, checked_usize, usize, 8);

pub fn signed_start(bytes: &[u8]) -> (bool, usize) {
 if bytes.is_empty() { return (false, 0); }
 if bytes[0] == b'+' { return (false, 1); }
 if bytes[0] == b'-' { return (true, 1); }
 (false, 0)
}
macro_rules! signed_path {
 ($tail:ident,$unchecked:ident,$checked:ident,$op:ident,$ty:ty,$bytes:expr) => {
 pub fn $unchecked(bytes: &[u8],mut value:$ty,mut cursor:usize,radix:u32)->Result<$ty,Error>{
  let mut iter=bytes.iter();
  while let Some(&c)=iter.next(){
   cursor+=1;
   let digit=match char_to_digit_const(c,radix){Some(d)=>d,None=>return Err(Error::InvalidDigit(cursor-1))};
   value=value.wrapping_mul(radix as $ty).$op(digit as $ty);
  }
  Ok(value)
 }
 pub fn $tail(bytes:&[u8],cursor:usize,radix:u32)->Result<$ty,Error>{
  if cursor==bytes.len(){return Err(Error::Empty(cursor));}
  let digits=&bytes[cursor..];
  let count=overflow_digits($bytes,true,radix);
  if digits.len()<=count{return $unchecked(digits,0,cursor,radix);}
  let value=$unchecked(&digits[..count],0,cursor,radix)?;
  checked::$checked(&digits[count..],value,cursor+count,radix)
 }
 };
}
macro_rules! signed_front {
 ($front:ident,$positive:ident,$negative:ident,$ty:ty)=>{
 pub fn $front(bytes:&[u8],radix:u32)->Result<$ty,Error>{
  let (negative,cursor)=signed_start(bytes);
  if negative{$negative(bytes,cursor,radix)}else{$positive(bytes,cursor,radix)}
 }
 };
}
signed_path!(complete_i8_positive_from_cursor,unchecked_i8_positive,checked_i8_positive,wrapping_add,i8,1);
signed_path!(complete_i8_negative_from_cursor,unchecked_i8_negative,checked_i8_negative,wrapping_sub,i8,1);
signed_front!(complete_i8,complete_i8_positive_from_cursor,complete_i8_negative_from_cursor,i8);
signed_path!(complete_i16_positive_from_cursor,unchecked_i16_positive,checked_i16_positive,wrapping_add,i16,2);
signed_path!(complete_i16_negative_from_cursor,unchecked_i16_negative,checked_i16_negative,wrapping_sub,i16,2);
signed_front!(complete_i16,complete_i16_positive_from_cursor,complete_i16_negative_from_cursor,i16);
signed_path!(complete_i32_positive_from_cursor,unchecked_i32_positive,checked_i32_positive,wrapping_add,i32,4);
signed_path!(complete_i32_negative_from_cursor,unchecked_i32_negative,checked_i32_negative,wrapping_sub,i32,4);
signed_front!(complete_i32,complete_i32_positive_from_cursor,complete_i32_negative_from_cursor,i32);
signed_path!(complete_i64_positive_from_cursor,unchecked_i64_positive,checked_i64_positive,wrapping_add,i64,8);
signed_path!(complete_i64_negative_from_cursor,unchecked_i64_negative,checked_i64_negative,wrapping_sub,i64,8);
signed_front!(complete_i64,complete_i64_positive_from_cursor,complete_i64_negative_from_cursor,i64);
signed_path!(complete_i128_positive_from_cursor,unchecked_i128_positive,checked_i128_positive,wrapping_add,i128,16);
signed_path!(complete_i128_negative_from_cursor,unchecked_i128_negative,checked_i128_negative,wrapping_sub,i128,16);
signed_front!(complete_i128,complete_i128_positive_from_cursor,complete_i128_negative_from_cursor,i128);
signed_path!(complete_isize_positive_from_cursor,unchecked_isize_positive,checked_isize_positive,wrapping_add,isize,8);
signed_path!(complete_isize_negative_from_cursor,unchecked_isize_negative,checked_isize_negative,wrapping_sub,isize,8);
signed_front!(complete_isize,complete_isize_positive_from_cursor,complete_isize_negative_from_cursor,isize);

macro_rules! unsigned_partial_front {
 ($front:ident,$tail:ident,$unchecked:ident,$checked:ident,$ty:ty,$bytes:expr)=>{
 pub fn $unchecked(bytes:&[u8],mut value:$ty,mut cursor:usize,radix:u32)->Result<($ty,usize),Error>{
  let mut iter=bytes.iter();
  while let Some(&c)=iter.next(){
   cursor+=1;
   let digit=match char_to_digit_const(c,radix){Some(d)=>d,None=>return Ok((value,cursor-1))};
   value=value.wrapping_mul(radix as $ty).wrapping_add(digit as $ty);
  }
  Ok((value,cursor))
 }
 pub fn $tail(bytes:&[u8],cursor:usize,radix:u32)->Result<($ty,usize),Error>{
  if cursor==bytes.len(){return Err(Error::Empty(cursor));}
  let digits=&bytes[cursor..];
  let count=overflow_digits($bytes,false,radix);
  if digits.len()<=count{return $unchecked(digits,0,cursor,radix);}
  let (value,ended)=$unchecked(&digits[..count],0,cursor,radix)?;
  if ended<cursor+count{return Ok((value,ended));}
  checked::partial::$checked(&digits[count..],value,cursor+count,radix)
 }
 pub fn $front(bytes:&[u8],radix:u32)->Result<($ty,usize),Error>{
  $tail(bytes,unsigned_start(bytes),radix)
 }
 };
}
unsigned_partial_front!(partial_u8,partial_u8_from_cursor,unchecked_u8_partial,checked_u8_partial,u8,1);
unsigned_partial_front!(partial_u16,partial_u16_from_cursor,unchecked_u16_partial,checked_u16_partial,u16,2);
unsigned_partial_front!(partial_u32,partial_u32_from_cursor,unchecked_u32_partial,checked_u32_partial,u32,4);
unsigned_partial_front!(partial_u64,partial_u64_from_cursor,unchecked_u64_partial,checked_u64_partial,u64,8);
unsigned_partial_front!(partial_u128,partial_u128_from_cursor,unchecked_u128_partial,checked_u128_partial,u128,16);
unsigned_partial_front!(partial_usize,partial_usize_from_cursor,unchecked_usize_partial,checked_usize_partial,usize,8);

macro_rules! signed_partial_path {
 ($tail:ident,$unchecked:ident,$checked:ident,$op:ident,$ty:ty,$bytes:expr)=>{
 pub fn $unchecked(bytes:&[u8],mut value:$ty,mut cursor:usize,radix:u32)->Result<($ty,usize),Error>{
  let mut iter=bytes.iter();
  while let Some(&c)=iter.next(){
   cursor+=1;
   let digit=match char_to_digit_const(c,radix){Some(d)=>d,None=>return Ok((value,cursor-1))};
   value=value.wrapping_mul(radix as $ty).$op(digit as $ty);
  }
  Ok((value,cursor))
 }
 pub fn $tail(bytes:&[u8],cursor:usize,radix:u32)->Result<($ty,usize),Error>{
  if cursor==bytes.len(){return Err(Error::Empty(cursor));}
  let digits=&bytes[cursor..];
  let count=overflow_digits($bytes,true,radix);
  if digits.len()<=count{return $unchecked(digits,0,cursor,radix);}
  let (value,ended)=$unchecked(&digits[..count],0,cursor,radix)?;
  if ended<cursor+count{return Ok((value,ended));}
  checked::partial::$checked(&digits[count..],value,cursor+count,radix)
 }
 };
}
macro_rules! signed_partial_front {
 ($front:ident,$positive:ident,$negative:ident,$ty:ty)=>{
 pub fn $front(bytes:&[u8],radix:u32)->Result<($ty,usize),Error>{
  let (negative,cursor)=signed_start(bytes);
  if negative{$negative(bytes,cursor,radix)}else{$positive(bytes,cursor,radix)}
 }
 };
}
signed_partial_path!(partial_i8_positive_from_cursor,unchecked_i8_positive_partial,checked_i8_positive_partial,wrapping_add,i8,1);
signed_partial_path!(partial_i8_negative_from_cursor,unchecked_i8_negative_partial,checked_i8_negative_partial,wrapping_sub,i8,1);
signed_partial_front!(partial_i8,partial_i8_positive_from_cursor,partial_i8_negative_from_cursor,i8);
signed_partial_path!(partial_i16_positive_from_cursor,unchecked_i16_positive_partial,checked_i16_positive_partial,wrapping_add,i16,2);
signed_partial_path!(partial_i16_negative_from_cursor,unchecked_i16_negative_partial,checked_i16_negative_partial,wrapping_sub,i16,2);
signed_partial_front!(partial_i16,partial_i16_positive_from_cursor,partial_i16_negative_from_cursor,i16);
signed_partial_path!(partial_i32_positive_from_cursor,unchecked_i32_positive_partial,checked_i32_positive_partial,wrapping_add,i32,4);
signed_partial_path!(partial_i32_negative_from_cursor,unchecked_i32_negative_partial,checked_i32_negative_partial,wrapping_sub,i32,4);
signed_partial_front!(partial_i32,partial_i32_positive_from_cursor,partial_i32_negative_from_cursor,i32);
signed_partial_path!(partial_i64_positive_from_cursor,unchecked_i64_positive_partial,checked_i64_positive_partial,wrapping_add,i64,8);
signed_partial_path!(partial_i64_negative_from_cursor,unchecked_i64_negative_partial,checked_i64_negative_partial,wrapping_sub,i64,8);
signed_partial_front!(partial_i64,partial_i64_positive_from_cursor,partial_i64_negative_from_cursor,i64);
signed_partial_path!(partial_i128_positive_from_cursor,unchecked_i128_positive_partial,checked_i128_positive_partial,wrapping_add,i128,16);
signed_partial_path!(partial_i128_negative_from_cursor,unchecked_i128_negative_partial,checked_i128_negative_partial,wrapping_sub,i128,16);
signed_partial_front!(partial_i128,partial_i128_positive_from_cursor,partial_i128_negative_from_cursor,i128);
signed_partial_path!(partial_isize_positive_from_cursor,unchecked_isize_positive_partial,checked_isize_positive_partial,wrapping_add,isize,8);
signed_partial_path!(partial_isize_negative_from_cursor,unchecked_isize_negative_partial,checked_isize_negative_partial,wrapping_sub,isize,8);
signed_partial_front!(partial_isize,partial_isize_positive_from_cursor,partial_isize_negative_from_cursor,isize);
