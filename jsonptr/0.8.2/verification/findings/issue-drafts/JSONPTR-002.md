# Pointer::get overflows when the excluded start bound is usize::MAX

## Description

`Pointer::get` can panic or return the wrong slice when a tuple of bounds
uses `Excluded(usize::MAX)` as its start bound.

## Steps to Reproduce

Use jsonptr 0.8.2 and run the example with both `cargo run` and
`cargo run --release`.

```rust
use jsonptr::Pointer;
use std::ops::Bound::{Excluded, Unbounded};

fn main() {
    let pointer = Pointer::from_static("/one/two");
    let result = pointer.get((Excluded(usize::MAX), Unbounded));
    assert_eq!(result, None);
}
```

## Expected Behavior

The call returns `None` because no token index can exceed `usize::MAX`.

## Actual Behavior

The default debug build panics with `attempt to add with overflow`.
The default release build returns `Some` containing `"/one/two"` and the
assertion fails.

## Environment

Rust 1.91.0 on aarch64 macOS. No optional jsonptr features are needed.
