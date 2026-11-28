# EncodingError::offset documentation does not match its value for tilde errors

## Description

The public field `EncodingError::offset` is documented as the "offset of
the erroneous `~` from within the `Token`". For `InvalidEncoding::Tilde`,
the value is the offset of the byte after the tilde. For a final tilde it
is the token length.

| `Token::from_encoded` input | Tilde offset | `offset` field |
| --- | --- | --- |
| `"a~b"` | 1 | 2 |
| `"~"` | 0 | 1 |
| `"~~"` | 0 | 1 |
| `"invalid~tilde"` | 7 | 8 |

The value itself is used consistently. `EncodingError::labels` places
its "must be 0 or 1" label at this offset, which is the byte after the
tilde. It labels a final tilde at this offset minus one.
`Pointer::parse("/a~b")` reports `source_offset()` 2. That is the same
number, measured from the `/` that starts the token. The crate's own tests
also expect these values. For `InvalidEncoding::Slash` the field is the
offset of the slash.

## Steps to Reproduce

Run this example with jsonptr 0.8.2. The assertion follows the field
documentation.

```rust
use jsonptr::Token;

fn main() {
    let input = "a~b";
    let error = Token::from_encoded(input).unwrap_err();
    assert_eq!(error.offset, input.find('~').unwrap());
}
```

## Expected Behavior

The documentation and the value agree. Since `labels`, `ParseError` and
the tests rely on the current value, updating the documentation looks
like the smaller change. For example, the field could be described as the
byte offset just after the tilde (the token length for a final tilde), or
the offset of the slash for `Slash` errors.

## Actual Behavior

The assertion fails: `error.offset` is 2, while the tilde is at offset 1.

## Environment

Rust 1.91.0 on aarch64 macOS, debug and release. No optional jsonptr
features are needed.
