# Pointer::strip_prefix still returns a malformed Pointer in 0.8.2

I can reproduce the partial-token prefix bug from #131 in jsonptr 0.8.2.
`Pointer::strip_prefix` returns a `Pointer` whose string fails the crate's
own parser.

```rust
use jsonptr::Pointer;

fn main() {
    let pointer = Pointer::from_static("/ab");
    let prefix = Pointer::from_static("/a");
    assert!(pointer.strip_prefix(prefix).is_none());
}
```

The assertion fails because the result is `Some` containing `"b"`. The
pointer has one token, `ab`, so there is no initial token `a` to remove.
`pointer.starts_with(prefix)` already returns `false`.

The separator check in the open pull request #132 would make this example
return `None`.

Reproduced with Rust 1.91.0 on aarch64 macOS in debug and release.
