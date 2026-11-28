# jsonptr 0.8.2 verification results

Managed run `.work/runs/default-lhpdidha` passed on `aarch64-apple-darwin`
(2026-11-28): exact regeneration of the extracted model, standard Lake build,
the named theorem audit of 27 theorems, and identical before/after input
fingerprints. The command was
`PATH=/opt/homebrew/opt/rustup/bin:$PATH bash scripts/verify.sh --offline`
from the version root. These are results for that run's inputs.

Every theorem in this profile is about the **unchanged release body**. Each
mapped contract requires the translated computation to return an Aeneas
success containing the specified Rust value or Rust error. The audit allows
only `propext`, `Classical.choice` and `Quot.sound`.

## Formally checked release APIs

`proofs.toml` maps these 20 entries; each theorem is the full intended
contract unless a premise is shown.

| Rust body | Audited behavior | Premise |
| --- | --- | --- |
| `pointer::validate_bytes` (private kernel) | For every nonempty byte slice at offset zero, accept the slash-and-escape grammar, report a missing leading slash, or report the first invalid tilde with exact separator and token-relative offsets. | offset 0, nonempty |
| `Index::for_len`, `for_len_incl`, `for_len_unchecked` | Strict and inclusive bounds over every index variant and machine length, with exact error fields. | none |
| `Index`: `PartialEq`, `Clone`, `Ord`/`PartialOrd`, `From<usize>` | Structural equality, exact copy, derived order (`Num` by value, then `Next`), `Num(n)`. | none |
| `OutOfBoundsError`, `InvalidCharacterError`, `InvalidEncoding`, `EncodingError`, `ParseError`, `ReplaceError`: `Clone`/`PartialEq` as derived | Exact copy and field-wise equality. `InvalidCharacterError::offset` returns the field. | none |
| `ParseError` accessors (`offset`, `pointer_offset`, `source_offset`, `is_no_leading_slash`, `is_no_leading_backslash`, `is_invalid_encoding`) | Exact field or variant observation. | none |
| `ParseError::complete_offset` | Returns pointer offset plus source offset. | the sum fits in `usize` |
| `EncodingError` and `assign::Error`: `Diagnostic::url` | The correct docs.rs address. | none |
| `Label::new`; `Report::original`, `into_original`, `decompose`; `Pointer::as_str` | Exact field construction and projection. | none |

The bodies were extracted with features `resolve` and `assign` in addition to
the earlier no-default-feature selection, so that the `resolve::Error` and
`assign::Error` items exist. Optimized MIR and stripped MIR local names are
kept, as before.

## Checked refutations on release bodies

These theorems negate an intended contract on the unchanged release body; the
corresponding APIs are not mapped.

| Intended contract | Theorem | Finding |
| --- | --- | --- |
| `complete_offset` succeeds for every error value | `completeOffsetTotal_refuted` | [JSONPTR-008](../../../verification/findings/JSONPTR-008.md) |
| `resolve::Error::url` names the `resolve` page | `resolveErrorUrl_refuted` | [JSONPTR-006](../../../verification/findings/JSONPTR-006.md) |
| `ParseIndexError::url` names `index/enum.ParseIndexError.html` | `parseIndexErrorUrl_refuted` | JSONPTR-006 |
| `ParseError::url` names `enum.ParseError.html` | `parseErrorUrl_refuted` | JSONPTR-006 |

## Boundaries with the unchanged verifier

Every remaining core operation (public parse, token codec, index parsing,
splitting, resolution, buffers, mutation, labels) fails extraction on its
release body: `str::as_bytes` reference transmute, raw-pointer dereference,
iterator and borrow-state errors, `core::str::pattern` signatures, `String`
and `ParseIntError` axioms, `serde_json` items. The separate
[adapted profile](../adapted/results.md) proves byte-level rewrites of those
bodies; those theorems are not release API claims. The `Diagnostic` trait
structure itself fails Lean universe inference in the generated model, so
generic `Report::subject`, `Deref`, `into_report` and `diagnose` are not
proved. `Display`/`Debug` output (the backend `Formatter` model discards
written text), `Error::source` (`dyn Error` needs axioms), hashing, raw casts
and serde/serde_json/toml/miette behaviour are excluded; see the
[API inventory](../adapted/api-inventory.md).

## Native release tests

In the same run, default features passed 99 unit tests and 49 doctests; all
features passed 105 unit tests and 49 doctests. Native outcomes are separate
from the Lean audit. Release defects found during verification are recorded in
[verification/findings](../../../verification/findings/README.md).

## Publication

The standard CLI (official cargo-proofs 0.4.1 built from proofs-rs
`3746712b39f2a45d8c067d24d83f767997040cae`) recorded run
`7a30a5ab-04b0-4b76-b969-bdbb16b7d5a7` against published source commit
`b6efd9dde6d748e6ce193a5e604e835a6d409c26` (branch `publication/jsonptr-0.8.2`),
using the CLI-facing package in [`publication/`](../../../publication). All 29
mapped theorems passed with only `propext`, `Classical.choice` and `Quot.sound`.

[Report #41](https://proofs.rs/report/41), revision 1, is public (2026-11-28).
Read-back through its public API confirms 29 claims and 8 findings; all report
prose fields and every finding title and body exactly match the local
`publication/proofs.toml`. The `Report` accessor theorem is audited locally but
not a recorded claim, because the recorder does not discover methods on the
generic `Report` impl. Adapted-profile theorems are described in the report as
supporting local work only. Local publication receipts and API responses remain
in ignored `.work/publication/`; managed-run archives remain local-only.
