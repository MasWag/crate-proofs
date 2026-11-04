extern crate alloc;
use creusot_std::prelude::*;
use creusot_std::prelude::{Clone, PartialEq};
pub fn resize(v: &mut Vec<u8>, n: usize) { v.resize(n, 0); }
pub fn truncate(v: &mut Vec<u8>, n: usize) { v.truncate(n); }
pub fn as_mut_slice(v: &mut Vec<u8>) -> &mut [u8] { v.as_mut_slice() }
pub fn into_bytes(s: String) -> Vec<u8> { s.into_bytes() }
pub fn from_utf8(v: Vec<u8>) -> Result<String, std::string::FromUtf8Error> { String::from_utf8(v) }
pub unsafe fn as_bytes_mut(s: &mut str) -> &mut [u8] { s.as_bytes_mut() }
#[derive(Clone, Copy, PartialEq, Eq, Debug, DeepModel)]
pub struct Derived { pub value: u8 }
pub fn display(f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result { f.write_str("error") }
#[ensures((^v)@.len() == n@)]
pub fn adapted_resize(v: &mut Vec<u8>, n: usize) {
    while v.len() < n { v.push(0); }
    #[invariant(v@.len() >= n@)]
    while v.len() > n { v.pop(); }
}
#[ensures(result@ == v@)]
#[ensures((^result)@ == (^v)@)]
pub fn adapted_slice(v: &mut Vec<u8>) -> &mut [u8] { &mut v[..] }
mod vec_utils;
pub fn utf8_guard_step(v: &[u8]) -> usize {
    match core::str::from_utf8(v) {
        Ok(_) => v.len(),
        Err(e) => { let _ = e.error_len(); e.valid_up_to() }
    }
}
pub fn sha_digest(v: &[u8]) {
    use sha2::{Digest, Sha256};
    let _ = Sha256::digest(v);
}
pub fn sha_update(v: &[u8]) {
    use sha2::{Digest, Sha256};
    let mut hash = Sha256::new();
    hash.update(v);
    let _ = hash.finalize();
}
pub fn string_push_ascii(bytes: &[u8]) -> String {
    let mut result = String::new();
    for byte in bytes { result.push(*byte as char); }
    result
}
