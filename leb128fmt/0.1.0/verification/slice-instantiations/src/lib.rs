#![no_std]

macro_rules! writer_probes {
    ($type:ty, $codec:ident, $fixed_codec:ident, $writer:ident, $fixed:ident) => {
        pub fn $writer<const BITS: u32>(
            value: $type,
            output: &mut [u8],
            pos: &mut usize,
        ) -> Option<usize> {
            leb128fmt::$codec::<$type, BITS>(value, output, pos)
        }

        pub fn $fixed<const BITS: u32>(
            value: $type,
            output: &mut [u8],
            pos: &mut usize,
        ) -> Option<usize> {
            leb128fmt::$fixed_codec::<$type, BITS>(value, output, pos)
        }
    };
}

macro_rules! reader_probe {
    ($type:ty, $codec:ident, $reader:ident) => {
        pub fn $reader<const BITS: u32>(
            input: &[u8],
            pos: &mut usize,
        ) -> Result<$type, leb128fmt::Error> {
            leb128fmt::$codec::<$type, BITS>(input, pos)
        }
    };
}

writer_probes!(u8, encode_uint_slice, encode_fixed_uint_slice, u8_writer, u8_fixed);
reader_probe!(u8, decode_uint_slice, u8_reader);
writer_probes!(u16, encode_uint_slice, encode_fixed_uint_slice, u16_writer, u16_fixed);
reader_probe!(u16, decode_uint_slice, u16_reader);
writer_probes!(u32, encode_uint_slice, encode_fixed_uint_slice, u32_writer, u32_fixed);
reader_probe!(u32, decode_uint_slice, u32_reader);
writer_probes!(u64, encode_uint_slice, encode_fixed_uint_slice, u64_writer, u64_fixed);
reader_probe!(u64, decode_uint_slice, u64_reader);
writer_probes!(u128, encode_uint_slice, encode_fixed_uint_slice, u128_writer, u128_fixed);
reader_probe!(u128, decode_uint_slice, u128_reader);
writer_probes!(i8, encode_sint_slice, encode_fixed_sint_slice, i8_writer, i8_fixed);
writer_probes!(i16, encode_sint_slice, encode_fixed_sint_slice, i16_writer, i16_fixed);
reader_probe!(i16, decode_sint_slice, i16_reader);
writer_probes!(i32, encode_sint_slice, encode_fixed_sint_slice, i32_writer, i32_fixed);
reader_probe!(i32, decode_sint_slice, i32_reader);
writer_probes!(i64, encode_sint_slice, encode_fixed_sint_slice, i64_writer, i64_fixed);
reader_probe!(i64, decode_sint_slice, i64_reader);
writer_probes!(i128, encode_sint_slice, encode_fixed_sint_slice, i128_writer, i128_fixed);
reader_probe!(i128, decode_sint_slice, i128_reader);
