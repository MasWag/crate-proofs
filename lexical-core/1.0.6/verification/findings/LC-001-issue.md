# [BUG] Partial parsing omits a single zero from the consumed length

## Description

`lexical_core::parse_partial_with_options` reports too few consumed bytes for a single integer zero when the format sets `no_integer_leading_zeros(true)`. The input is valid: forbidding leading zeros still permits a single zero. The same applies to the lexical-core integer `FromLexicalWithOptions::from_lexical_partial_with_options` implementations.

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
```

## Additional Context

The assertion fails with `left: Ok((0, 0))`, `right: Ok((0, 1))`. Signed `b"-0"` similarly returns `Ok((0, 1))` instead of `Ok((0, 2))`. Standard-format `parse_partial::<u8>(b"0")` returns `Ok((0, 1))`, and the custom format consumes one byte for `b"0!"`.

This is the existing symptom in [#225](https://github.com/Alexhuszagh/rust-lexical/issues/225), reproduced here through lexical-core 1.0.6. No new upstream issue has been filed.
