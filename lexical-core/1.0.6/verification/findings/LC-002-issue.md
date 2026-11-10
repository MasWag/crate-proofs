# [BUG] Suffix format advances past an unrelated invalid byte

## Description

With a base suffix configured, `lexical_core::parse_partial_with_options` can count an unrelated invalid byte as consumed when another byte follows it. `lexical_core::parse_with_options` then reports the following byte as the invalid digit. The configured suffix in the example is `h`; `?` should terminate the number at index 2. The lexical-core integer `FromLexicalWithOptions` methods forward to the same parser.

## Prerequisites

- Rust version: `rustc 1.94.1 (e408947bf 2026-03-25)`
- lexical-core version: `1.0.6` (resolving lexical-parse-integer `1.0.6` and lexical-util `1.0.7`)
- Features: `parse-integers`, `format`, `power-of-two`; default features disabled

```toml
[dependencies]
lexical-core = { version = "=1.0.6", default-features = false, features = ["parse-integers", "format", "power-of-two"] }
```

## Test case

```rust
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
```

## Additional Context

The assertion fails with `left: Ok((12, 3))`, `right: Ok((12, 2))`. For the same input and format, complete parsing returns `Err(InvalidDigit(3))` instead of `Err(InvalidDigit(2))`.

Controls: `b"12?"` consumes two bytes; `b"12h?"` consumes three bytes, including the actual suffix. The extra consumption occurs when an unrelated invalid byte has another byte after it.
