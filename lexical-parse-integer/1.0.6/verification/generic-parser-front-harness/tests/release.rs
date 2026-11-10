use release::{FromLexicalWithOptions, Options};
use lexical_util::format::NumberFormatBuilder;
use lexical_parse_integer_generic_front_harness as h;
fn encode(mut n:u128,radix:u32)->Vec<u8>{let mut v=Vec::new(); loop {let d=(n%radix as u128)as u8;v.push(if d<10{b'0'+d}else{b'A'+d-10});n/=radix as u128;if n==0{break}}v.reverse();v}
macro_rules! check_radix {($r:literal)=>{{
 const F:u128=NumberFormatBuilder::from_radix($r);
 let options=Options::builder().no_multi_digit(true).build_strict();
 macro_rules! check_type {($ty:ty,$front:ident,$partial:ident)=>{{
  let mut cases=vec![b"".to_vec(),b"+".to_vec(),b"-1".to_vec(),b"++1".to_vec(),b"12?345".to_vec(),b"+?12345".to_vec(),vec![255,0,48]];
  for n in [0,1,9,127,128,255,256,<$ty>::MAX as u128] {let v=encode(n,$r);cases.push(v.clone());let mut plus=vec![b'+'];plus.extend(&v);cases.push(plus);let mut long=v.clone();long.extend([b'0';40]);cases.push(long);let mut bad=v;bad.push(b'?');bad.extend([b'9';40]);cases.push(bad);}
  for c in cases {assert_eq!(h::$partial(&c,$r),<$ty>::from_lexical_partial_with_options::<F>(&c,&options),"partial radix {} type {} input {:?}",$r,stringify!($ty),c);assert_eq!(h::$front(&c,$r),<$ty>::from_lexical_with_options::<F>(&c,&options),"radix {} type {} input {:?}",$r,stringify!($ty),c);}
 }};}
 macro_rules! signed_type {($ty:ty,$front:ident,$partial:ident)=>{{
  let mut cases=vec![b"".to_vec(),b"+".to_vec(),b"-".to_vec(),b"-+1".to_vec(),b"--1".to_vec(),b"+?12345".to_vec(),b"-?12345".to_vec(),b"1?12345".to_vec(),vec![255,48]];
  for n in [0,1,127,128,<$ty>::MAX as u128, (<$ty>::MAX as u128)+1] {
   let v=encode(n,$r);cases.push(v.clone());
   for sign in [b'+',b'-'] {let mut x=vec![sign];x.extend(&v);cases.push(x.clone());let mut bad=x.clone();bad.push(b'?');bad.extend([b'9';40]);cases.push(bad);x.extend([b'0';40]);cases.push(x);}
  }
  for c in cases {assert_eq!(h::$front(&c,$r),<$ty>::from_lexical_with_options::<F>(&c,&options),"signed radix {} type {} input {:?}",$r,stringify!($ty),c);assert_eq!(h::$partial(&c,$r),<$ty>::from_lexical_partial_with_options::<F>(&c,&options),"signedpartial radix {} type {} input {:?}",$r,stringify!($ty),c);}
 }};}
 signed_type!(i8,complete_i8,partial_i8);signed_type!(i16,complete_i16,partial_i16);signed_type!(i32,complete_i32,partial_i32);signed_type!(i64,complete_i64,partial_i64);signed_type!(i128,complete_i128,partial_i128);signed_type!(isize,complete_isize,partial_isize);
 check_type!(u8,complete_u8,partial_u8);check_type!(u16,complete_u16,partial_u16);check_type!(u32,complete_u32,partial_u32);check_type!(u64,complete_u64,partial_u64);check_type!(u128,complete_u128,partial_u128);check_type!(usize,complete_usize,partial_usize);
}};}
#[test] fn standard_unsigned_front_all_radices(){
check_radix!(2);
check_radix!(3);
check_radix!(4);
check_radix!(5);
check_radix!(6);
check_radix!(7);
check_radix!(8);
check_radix!(9);
check_radix!(10);
check_radix!(11);
check_radix!(12);
check_radix!(13);
check_radix!(14);
check_radix!(15);
check_radix!(16);
check_radix!(17);
check_radix!(18);
check_radix!(19);
check_radix!(20);
check_radix!(21);
check_radix!(22);
check_radix!(23);
check_radix!(24);
check_radix!(25);
check_radix!(26);
check_radix!(27);
check_radix!(28);
check_radix!(29);
check_radix!(30);
check_radix!(31);
check_radix!(32);
check_radix!(33);
check_radix!(34);
check_radix!(35);
check_radix!(36);
}
