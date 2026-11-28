// These tests assert the observed release bugs; passing does not mean conformance.
leb128fmt::encode_fixed_uint_arr!(encode_fixed_u7, u32, 7);
leb128fmt::decode_uint_arr!(decode_u7, u32, 7);

#[test]
fn fixed_seven_bit_encoder_panics_on_zero() {
    assert!(std::panic::catch_unwind(|| encode_fixed_u7(0)).is_err());
}

#[test]
fn seven_bit_decoder_panics_on_unterminated_input() {
    assert!(std::panic::catch_unwind(|| decode_u7([0x80])).is_err());
}

#[test]
fn seven_bit_decoder_accepts_valid_terminal_byte() {
    assert_eq!(decode_u7([0x7f]), Some((127, 1)));
}
