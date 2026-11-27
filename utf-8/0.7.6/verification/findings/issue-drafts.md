# Issue drafts

These drafts have not been submitted. The upstream repository is archived.

## Document state requirements for Incomplete::try_complete

### Description

`Incomplete::try_complete` can panic when an `Incomplete` is constructed with bytes that are not an incomplete UTF-8 suffix. The constructor and fields are public, but their required state is not documented. Could the allowed states and panic behavior be documented, or should this input be handled differently?

### Steps to Reproduce

With `utf-8 = "=0.7.6"`, run:

```rust
let mut state = utf8::Incomplete::new(&[0x61, 0xff]);
let _ = state.try_complete(&[]);
```

### Expected Behavior

The API should specify whether such a manually constructed state is permitted and what happens when completing it.

### Actual Behavior

The call panics when a checked subtraction returns `None` and is unwrapped.

### Environment

`utf-8` 0.7.6, rustc 1.91.0, default unoptimized build.

### Screenshots/Logs

`called Option::unwrap() on a None value`

### Additional Context

The documented workflow passes an incomplete suffix from `decode`; this example does not show that workflow failing. An empty state or proper incomplete UTF-8 prefix avoids this particular issue.

## Clarify retry behavior after a buffer fill error

### Description

`BufReadDecoder::next_strict` can skip an unread byte on retry when the underlying `BufRead` returns a transient error on its second `fill_buf` call. Is retry after an I/O error intended to preserve unread input?

### Steps to Reproduce

With `utf-8 = "=0.7.6"`, run the following. Successful execution reproduces the discrepancy:

```rust
extern crate utf8;
use std::io::{self, BufRead, ErrorKind, Read};

/// A position-preserving read of a single-byte source, interrupted on its second read.
struct Source {
    reads: usize,
}
impl Read for Source {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        self.reads += 1;
        if self.reads == 2 { return Err(ErrorKind::Interrupted.into()); }
        if out.is_empty() { return Ok(0); }
        out[0] = b'x';
        Ok(1)
    }
}
struct Window {
    source: Source,
    preview: [u8; 1],
    consumed: bool,
}
impl BufRead for Window {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.consumed { return Ok(&[]); }
        // Refresh a view of the same byte without advancing the logical cursor.
        let count = self.source.read(&mut self.preview)?;
        Ok(&self.preview[..count])
    }
    fn consume(&mut self, count: usize) {
        assert!(count <= usize::from(!self.consumed));
        if count != 0 { self.consumed = true; }
    }
}
impl Read for Window {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if out.is_empty() { return Ok(0); }
        let count = self.fill_buf()?.read(out)?;
        self.consume(count);
        Ok(count)
    }
}
fn window() -> Window {
    Window { source: Source { reads: 0 }, preview: [0], consumed: false }
}
fn main() {
    let mut direct = window();
    assert_eq!(direct.fill_buf().unwrap(), b"x");
    assert_eq!(direct.fill_buf().unwrap_err().kind(), ErrorKind::Interrupted);
    assert_eq!(direct.fill_buf().unwrap(), b"x");
    let mut decoder = utf8::BufReadDecoder::new(window());
    match decoder.next_strict() {
        Some(Err(utf8::BufReadDecoderError::Io(e))) => assert_eq!(e.kind(), ErrorKind::Interrupted),
        other => panic!("unexpected {:?}", other)
    }
    // Success reproduces the missing byte on retry.
    assert!(decoder.next_strict().is_none());
}
```

### Expected Behavior

Please clarify whether retrying should return the byte that the reader has not consumed.

### Actual Behavior

The first decoder call returns `Interrupted`; retry returns `None`. Direct calls to the same reader return `x`, `Interrupted`, then `x` before a consume.

### Environment

`utf-8` 0.7.6, rustc 1.91.0, default unoptimized build.

### Screenshots/Logs

The assertions in the example pass.

### Additional Context

This uses a custom reader that preserves its logical position across the error. The example does not establish the behavior for `std::io::BufReader`.
