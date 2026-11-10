pub fn parse_u32(bytes: &[u8]) -> lexical_core::Result<u32> { lexical_core::parse(bytes) }
pub fn parse_f64(bytes: &[u8]) -> lexical_core::Result<f64> { lexical_core::parse(bytes) }
pub fn write_u32(value:u32, bytes:&mut [u8]) -> &mut [u8] { lexical_core::write(value,bytes) }
pub fn write_f64(value:f64, bytes:&mut [u8]) -> &mut [u8] { lexical_core::write(value,bytes) }
pub fn parse_partial_u32(bytes: &[u8]) -> lexical_core::Result<(u32, usize)> { lexical_core::parse_partial(bytes) }
pub fn parse_partial_f64(bytes: &[u8]) -> lexical_core::Result<(f64, usize)> { lexical_core::parse_partial(bytes) }
