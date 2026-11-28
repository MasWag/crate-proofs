// At width seven, the release can consume an extra zero group.
use leb128fmt::{decode_sint_slice, decode_uint_slice};

#[test]
fn signed_decoder_returns_a_value_above_the_seven_bit_maximum() {
    let mut pos = 0;
    let decoded = decode_sint_slice::<i16, 7>(&[0xff, 0x00], &mut pos);
    assert_eq!(decoded, Ok(127));
    assert_eq!(pos, 2);
}

#[test]
fn unsigned_decoder_consumes_two_groups_for_a_seven_bit_field() {
    let mut pos = 0;
    let decoded = decode_uint_slice::<u16, 7>(&[0xff, 0x00], &mut pos);
    assert_eq!(decoded, Ok(127));
    assert_eq!(pos, 2);
}

#[test]
fn continued_unsigned_one_bit_field_can_exceed_the_field_or_wrap_in_storage() {
    for (terminal, expected) in [(1, 128), (2, 0)] {
        let mut pos = 0;
        let decoded = decode_uint_slice::<u8, 1>(&[0x80, terminal], &mut pos);
        assert_eq!(decoded, Ok(expected));
        assert_eq!(pos, 2);
    }
}
