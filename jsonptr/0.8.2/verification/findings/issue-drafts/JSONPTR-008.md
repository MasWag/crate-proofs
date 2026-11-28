# Diagnostic helpers overflow on hand-built errors or mismatched subjects

## Description

Several diagnostic helpers use unchecked `usize` addition or subtraction. The error types
have public fields or variants, so these values can be built directly, and
the helpers also accept any subject string. With the inputs below, debug
builds panic with an overflow and release builds return wrapped numbers.

| Call | Debug | Release |
| --- | --- | --- |
| `ParseError::InvalidEncoding { offset: 0, source: EncodingError { offset: 1, source: Tilde } }.invalid_encoding_len("")` | `attempt to subtract with overflow` | `2` |
| `ParseError::InvalidEncoding { offset: usize::MAX, source: EncodingError { offset: 1, source: Tilde } }.complete_offset()` | `attempt to add with overflow` | `0` |
| `resolve::Error::NotFound { position: 0, offset: usize::MAX }.labels(&PointerBuf::parse("/a")?)` | `attempt to add with overflow` | label at offset 0, length 1 |
| `assign::Error::OutOfBounds { position: 0, offset: usize::MAX, source: OutOfBoundsError { length: 0, index: 1 } }.labels(&PointerBuf::parse("/a")?)` | `attempt to add with overflow` | label at offset 0, length 1 |
| `EncodingError { offset: 0, source: InvalidEncoding::Tilde }.labels(&String::new())` | `attempt to subtract with overflow` | label at offset `usize::MAX`, length 1 |

The `labels` calls are `Diagnostic::labels`. `ParseError::labels` calls
both `complete_offset` and `invalid_encoding_len`. I did not find a parse,
resolve or assign operation that produces these values, so this mainly
affects code that builds errors by hand or pairs an error with another
subject.

## Steps to Reproduce

Run this example with jsonptr 0.8.2, using both `cargo run` and
`cargo run --release`.

```rust
use jsonptr::{EncodingError, InvalidEncoding, ParseError};

fn main() {
    let error = ParseError::InvalidEncoding {
        offset: 0,
        source: EncodingError { offset: 1, source: InvalidEncoding::Tilde },
    };
    let subject = "";
    let len = error.invalid_encoding_len(subject);
    assert!(len <= subject.len(), "length {len} for an empty subject");
}
```

## Expected Behavior

The helpers return a value without panicking, such as a span limited to
the subject or no label. Alternatively, a documented precondition could
state which errors and subjects are valid.

## Actual Behavior

The debug build panics with `attempt to subtract with overflow`. The release
build returns 2 and the assertion fails.

## Environment

Rust 1.91.0 on aarch64 macOS. The `resolve` and `assign` features are
needed only for their error types.
