# ParseIndexError::InvalidCharacter label can extend past the token

## Description

The diagnostic label for `ParseIndexError::InvalidCharacter` can describe
a span outside the token, or one that ends inside a multi-byte character.

- When no ASCII digit follows the invalid character, the label length is
  the length of the whole token, not of the rest of it. For `"1abc"` the
  label starts at offset 1 with length 4, the span `1..5` in a four-byte
  token. `"1-"` gives `1..3` and `"1é"` gives `1..4` in a three-byte token.
- When a digit does follow, the length counts characters, while the label
  offsets of this crate and of `miette` are byte offsets. For `"aé1"` the
  label is `0..2`, which ends inside `é`. The non-digit run is three bytes.

The labels are returned by `Diagnostic::labels` for `ParseIndexError` and,
with the `miette` feature, by the `miette` labels of
`Report<ParseIndexError>`.

## Steps to Reproduce

Run this example with jsonptr 0.8.2.

```rust
use jsonptr::diagnostic::{Diagnostic, Label};
use jsonptr::index::Index;
use jsonptr::Diagnose;

fn main() {
    let input = String::from("1abc");
    let report = Index::try_from(input.as_str()).diagnose(input).unwrap_err();
    let (error, subject) = report.decompose();
    let labels: Vec<Label> = error.labels(&subject).unwrap().collect();
    assert_eq!(labels, [Label::new("invalid character(s)".into(), 1, 3)]);
}
```

## Expected Behavior

The label covers the non-digit bytes `abc`: offset 1, length 3. In general,
it should end at the next ASCII digit or at the end of the token, measured
in bytes. At minimum the span should stay inside the token and end on a
character boundary; the crate's own test expects (0, 3) for `"bar"`.

## Actual Behavior

The assertion fails because the label has offset 1 and length 4. With the
`miette` feature, printing this report as a `miette::Report` shows the
token but no "invalid character(s)" label text (seen with miette 7.4.0).

The length is right when the run starts at offset 0 and reaches the end,
as in `"bar"`, and for an ASCII run followed by a digit, as in `"1a2"`.

## Environment

Rust 1.91.0 on aarch64 macOS, debug and release. No optional jsonptr
features are needed.
