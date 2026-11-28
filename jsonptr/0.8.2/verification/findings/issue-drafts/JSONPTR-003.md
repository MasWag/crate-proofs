# A final bare tilde produces a diagnostic span past the end of the input

## Description

`ParseError::invalid_encoding_len` reports two bytes for a final bare tilde,
even when called with the original string that produced the error.

## Steps to Reproduce

Run this example with jsonptr 0.8.2.

```rust
use jsonptr::Pointer;

fn main() {
    let input = "/~";
    let error = Pointer::parse(input).unwrap_err();
    assert_eq!(error.complete_offset(), 1);
    assert_eq!(error.invalid_encoding_len(input), 1);
}
```

## Expected Behavior

The diagnostic spans one byte because only the tilde remains at offset 1.

## Actual Behavior

The last assertion fails because `invalid_encoding_len` returns 2. The span
would run from offset 1 to offset 3 in a two-byte string.

## Environment

Rust 1.91.0 on aarch64 macOS. No optional jsonptr features are needed.
