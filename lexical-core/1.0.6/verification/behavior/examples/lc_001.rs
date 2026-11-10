use lexical_core::{NumberFormatBuilder, ParseIntegerOptions};

fn main() {
    const FORMAT: u128 = NumberFormatBuilder::new()
        .no_integer_leading_zeros(true)
        .build_strict();
    let result = lexical_core::parse_partial_with_options::<u8, FORMAT>(
        b"0",
        &ParseIntegerOptions::new(),
    );
    assert_eq!(result, Ok((0, 1))); // actual: Ok((0, 0))
}
