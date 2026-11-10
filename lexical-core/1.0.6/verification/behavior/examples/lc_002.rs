use core::num::NonZeroU8;
use lexical_core::{NumberFormatBuilder, ParseIntegerOptions};

fn main() {
    const FORMAT: u128 = NumberFormatBuilder::new()
        .base_suffix(NonZeroU8::new(b'h'))
        .build_strict();
    let result = lexical_core::parse_partial_with_options::<u8, FORMAT>(
        b"12?x",
        &ParseIntegerOptions::new(),
    );
    assert_eq!(result, Ok((12, 2))); // actual: Ok((12, 3))
}
