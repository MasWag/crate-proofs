use block_padding::{Padding, Pkcs7, Iso10126, AnsiX923, ZeroPadding, Iso7816, NoPadding};
#[test]
fn empty_unpadding_release_behavior() {
    assert!(std::panic::catch_unwind(|| Pkcs7::raw_unpad(&[])).is_err());
    assert!(std::panic::catch_unwind(|| Iso10126::raw_unpad(&[])).is_err());
    assert!(std::panic::catch_unwind(|| AnsiX923::raw_unpad(&[])).is_err());
    assert_eq!(ZeroPadding::raw_unpad(&[]).unwrap(), &[]);
    assert_eq!(NoPadding::raw_unpad(&[]).unwrap(), &[]);
    assert!(Iso7816::raw_unpad(&[]).is_err());
}
