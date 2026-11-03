use block_padding::{Padding, Pkcs7};
#[test]
#[ignore = "Expected failure: reproduces release empty-input panic"]
fn malformed_empty_should_error() { assert!(Pkcs7::raw_unpad(&[]).is_err()); }
