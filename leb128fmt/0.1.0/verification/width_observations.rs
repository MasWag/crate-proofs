// Numeric observations of the original 0.1.0 release.
use leb128fmt::{decode_uint_slice, encode_fixed_sint_slice, encode_sint_slice};

#[test]
fn unsigned_one_bit_result_exceeds_the_requested_width() {
    let mut pos = 0;
    let result = decode_uint_slice::<u8, 1>(&[127], &mut pos);
    assert_eq!(result, Ok(127));
    assert_eq!(pos, 1);
}

#[test]
fn signed_slice_encoders_accept_one_above_the_maximum() {
    // A signed 8-bit field ends at 127. Both encoders accept 128.
    for encode in [
        encode_sint_slice::<i16, 8>,
        encode_fixed_sint_slice::<i16, 8>,
    ] {
        let mut output = [0; 2];
        let mut pos = 0;
        assert_eq!(encode(128, &mut output, &mut pos), Some(2));
        assert_eq!(output, [0x80, 0x01]);
        assert_eq!(pos, 2);
    }
}

#[test]
fn permissive_signed_width_guard_can_exceed_fixed_buffer() {
    // One byte is the documented capacity for a 7-bit field. The accepted
    // value 127 needs two signed groups and the fixed encoder tries both writes.
    let result = std::panic::catch_unwind(|| {
        let mut output = [0];
        let mut pos = 0;
        encode_fixed_sint_slice::<i16, 7>(127, &mut output, &mut pos)
    });
    assert!(result.is_err());
}
