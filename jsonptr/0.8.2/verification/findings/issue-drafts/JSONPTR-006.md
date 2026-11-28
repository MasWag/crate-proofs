# Diagnostic::url returns the wrong docs.rs page for three error types

## Description

`Diagnostic::url` is documented as "the docs.rs URL for this error". Three
of its five implementations return a URL for a different page:

| Type | Returned path after `https://docs.rs/jsonptr/0.8.2/jsonptr/` | Expected path |
| --- | --- | --- |
| `resolve::Error` | `assign/enum.Error.html` | `resolve/enum.Error.html` |
| `index::ParseIndexError` | `enum.ParseIndexError.html` | `index/enum.ParseIndexError.html` |
| `ParseError` | `struct.ParseError.html` | `enum.ParseError.html` |

`resolve::Error` returns the URL of `assign::Error`. `ParseIndexError` is
only public as `jsonptr::index::ParseIndexError`, but its URL omits the
`index` module. `ParseError` is an enum, but its URL names a struct page.
`assign::Error` and `EncodingError` return the expected URLs.

With the `miette` feature, `Report<T>` returns the same string from its
`miette::Diagnostic::url`.

## Steps to Reproduce

Run this example with jsonptr 0.8.2 and its default features.

```rust
use jsonptr::diagnostic::Diagnostic;
use jsonptr::index::ParseIndexError;
use jsonptr::{resolve, ParseError};

fn main() {
    let base = "https://docs.rs/jsonptr/0.8.2/jsonptr/";
    let actual = [
        <resolve::Error as Diagnostic>::url(),
        <ParseIndexError as Diagnostic>::url(),
        <ParseError as Diagnostic>::url(),
    ];
    let expected = [
        format!("{base}resolve/enum.Error.html"),
        format!("{base}index/enum.ParseIndexError.html"),
        format!("{base}enum.ParseError.html"),
    ];
    assert_eq!(actual, expected);
}
```

## Expected Behavior

Each URL names the type's own rustdoc page. rustdoc names an item page
`<kind>.<Name>.html` in the directory of the module that exposes it.
`ParseError` is a `pub enum` re-exported at the crate root,
`ParseIndexError` is a `pub enum` in `pub mod index` with no re-export, and
`resolve::Error` is a `pub enum` in `pub mod resolve`.

## Actual Behavior

The assertion fails and shows the three returned URLs from the table above.
I did not fetch the pages; a local `cargo doc` build produces the expected
paths.

## Environment

Rust 1.91.0 on aarch64 macOS, debug and release. The `resolve` feature is
needed for `resolve::Error`.
