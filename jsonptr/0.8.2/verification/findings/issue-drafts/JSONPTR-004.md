# ParseIndexError labels panic for an index made only of zeros

## Description

`Index` parsing rejects `"00"` with `ParseIndexError::LeadingZeros`, as
RFC 6901 requires. Asking that error for its diagnostic label then panics
with `starts with zeros`. Every token of two or more `'0'` characters is
affected, such as `"00"` and `"000"`.

The panic comes from `Diagnostic::labels` for `ParseIndexError`. With the
`miette` feature, `miette::Diagnostic::labels` on a
`Report<ParseIndexError>` calls the same code. Printing such a report as a
`miette::Report` panics after the error message is written.

## Steps to Reproduce

Run this example with jsonptr 0.8.2.

```rust
use jsonptr::diagnostic::Diagnostic;
use jsonptr::index::Index;
use jsonptr::Diagnose;

fn main() {
    let input = String::from("00");
    let report = Index::try_from(input.as_str()).diagnose(input).unwrap_err();
    let (error, subject) = report.decompose();
    let labels: Vec<_> = error.labels(&subject).unwrap().collect();
    assert_eq!(labels.len(), 1);
}
```

## Expected Behavior

`labels` returns one "leading zeros" label inside the input, as it does
for `"01"` (offset 0, length 1) and `"000001"` (offset 0, length 5).

## Actual Behavior

The call to `labels` panics with `starts with zeros` in debug and release
builds. The label length is the position of the first character that is
not `'0'`, found with `expect`. An all-zero token has no such character.

## Environment

Rust 1.91.0 on aarch64 macOS. No optional jsonptr features are needed.
The `miette` rendering panic was seen with miette 7.4.0 and the `miette`
feature.
