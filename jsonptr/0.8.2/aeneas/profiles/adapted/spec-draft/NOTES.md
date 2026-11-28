# Release-behaviour discrepancies noticed while specifying

Written by the specification agent on 2026-11-27 from the locked release source
`.work/source/src`. These are candidate findings. None has a record under
`verification/findings/` unless stated, and none was reported upstream.

The core algorithms targeted by the adapted profile showed no functional discrepancy:
pointer validation, token encoding, decoding and validation, index parsing, token
splitting and JSON resolution all agree with the model on the inputs probed. That is
source inspection plus a small native probe, not a proof. Every new candidate below is in
diagnostics or documentation.

## Native probe

A throwaway Cargo project in the session scratchpad depended on the untouched release by
path, with `default-features = false` and the `resolve` feature, so it had no external
dependencies. It ran once from `/private/tmp` with `cargo +1.91.0 run --offline` in the
debug profile on `aarch64-apple-darwin`. It called `Diagnostic::labels` directly and
caught panics with `catch_unwind`. The release profile and the miette rendering path were
not run. The probe is not kept in the repository; the primary should move anything worth
keeping into `verification/native/`.

## Already recorded

| Record | Relation to this round |
| --- | --- |
| JSONPTR-001, `strip_prefix` returns a malformed pointer | Outside the adapted targets. It means a `Pointer` reached through `strip_prefix` may break the premise of target 6. |
| JSONPTR-002, `Pointer::get` overflows on `Excluded(usize::MAX)` | Outside the adapted targets. |
| JSONPTR-003, a final bare tilde gives an out-of-bounds span | Same function as N5 below, different trigger. |

## New candidates

### N1. `ParseIndexError::labels` panics when the token is all zeros

- Input: `Index::from_str("00")` returns `Err(LeadingZeros)`. Then call `labels` on that
  error with the subject `"00"`.
- Expected: a label over the leading zeros, for example offset 0 and length 1.
- Release: panics with `starts with zeros` at `index.rs:376`. Confirmed natively for
  `"00"` and `"000"`.
- Cause: `subject.chars().position(|c| c != '0').expect(..)` at `index.rs:373–376` assumes
  a non-zero character follows. `"01"` and `"0a"` give offset 0, length 1 as expected.
- Reach: the public `Diagnostic::labels`, and by source inspection the miette `labels` of
  a `Report<ParseIndexError>`. Resolution errors do not call it.

### N2. `InvalidCharacter` label length runs past the subject and mixes units

- Input: `"1abc"`, which gives `InvalidCharacter` at offset 1.
- Expected: offset 1, length 3, the run of non-digit bytes.
- Release: offset 1, length 4, so the span is `1..5` in a four-byte subject. Confirmed
  natively. `"1-"` gives offset 1, length 2; `"1é"` gives offset 1, length 3 in a
  three-byte subject.
- Cause: `index.rs:381–385` falls back to `subject.len()`, the whole length, when no digit
  follows, instead of the remaining length.
- Second defect in the same lines: the length counts characters while spans are in bytes.
  `"aé1"` gives length 2, which ends inside the two-byte `é`; the byte length is 3.
  Confirmed natively.

### N3. `resolve::Error::url` points at the `assign` error page

- Input: `<jsonptr::resolve::Error as Diagnostic>::url()`.
- Expected: `https://docs.rs/jsonptr/0.8.2/jsonptr/resolve/enum.Error.html`.
- Release: `https://docs.rs/jsonptr/0.8.2/jsonptr/assign/enum.Error.html`. Confirmed
  natively.
- Cause: `resolve.rs:216` uses `diagnostic_url!(enum assign::Error)`, the same argument as
  `assign.rs:215`.

### N4. `EncodingError::offset` is documented as the tilde's offset but is one past it

- Input: `Token::from_encoded("a~b")`.
- Documented at `token.rs:399`: "offset of the erroneous `~` from within the `Token`",
  which would be 1.
- Release: offset 2, the byte after the tilde. `"~"` gives 1, `"~~"` gives 1 and
  `"invalid~tilde"` gives 8. Confirmed natively.
- Assessment: a documentation defect. The value is consistent across the crate.
  `EncodingError::labels` treats it as the byte after the tilde, and the pointer parser
  produces the same number as the tilde's distance from the separator: `"/a~b"` gives
  pointer offset 0 and source offset 2. The adapted specification keeps the release value.

### N5. `ParseError::invalid_encoding_len` underflows on an empty subject

- Input: a `ParseError::InvalidEncoding` value and the subject `""`.
- Expected: a length without a panic; 0 is the natural answer for an empty subject.
- Release: `attempt to subtract with overflow` at `pointer.rs:1200` in the debug profile.
  Confirmed natively. In the release profile the subtraction would wrap and the result
  would be 2; that was not run.
- Assessment: low severity. The subject does not match the error, since no parse of `""`
  fails. The variant is publicly constructible, so the default specification's
  arithmetic-domain obligation for public errors applies. It is the same function as
  JSONPTR-003 with a different trigger.

## Observations that are not findings

- `Index::from_str("0a")` returns `LeadingZeros`, not `InvalidCharacter`. The default
  specification already fixes this precedence.
- `Token::decoded` on bytes outside the image of the encoding, such as `"~a0"`, would
  give `"a~"` by source inspection. No safe constructor produces such a token, so this is
  unspecified behaviour and was not run.
- The doc comments of `is_unreachable`, `is_not_found` and `is_out_of_bounds` in
  `resolve.rs:187–201` all say `FailedToParseIndex`. The code is right.
- `Index::from_str` reports the character position of the first non-digit and the model
  reports the byte position. They agree because all earlier bytes are ASCII digits.
- Resolving `-` on an array gives `OutOfBounds` with `index = length`, which matches the
  RFC 6901 §4 error condition.

## Second round: the whole public API

Added on 2026-11-27 after reading every non-test line of `.work/source/src`, including
`pointer/slice.rs`, `assign.rs`, `delete.rs`, `diagnostic.rs` and `component.rs`.

### Probes

Two throwaway projects in the session scratchpad, both against the untouched release by
path, run from `/private/tmp` with `cargo +1.91.0 run --offline`, in the debug and the
release profile on `aarch64-apple-darwin`.

- The first-round probe, rerun in the release profile. N1 to N4 reproduce unchanged
  there. N5 does not panic there: `invalid_encoding_len("")` returns 2.
- A second probe with the features `resolve`, `assign`, `delete`, `json` and `std`, and
  `serde_json` from the offline registry cache. It printed range indexing, prefix and
  suffix operations, buffer mutation, 13 assignments and 8 deletions on
  `serde_json::Value`, and the hand-built error values below. Apart from N6 to N8 the
  two profiles printed the same results, and every result agrees with the closed test
  vectors in `SpecModel.lean`.

The probes are not kept in the repository. TOML and miette were not run.

### Status of the recorded findings in this round

- JSONPTR-001 reproduced again in both profiles: `"/ab"` minus `"/a"` gives `Some("b")`.
  It refutes the `strip_prefix` contract of section 11.
- JSONPTR-002 was not rerun. It refutes the tuple form in section 9.
- JSONPTR-003 was not rerun. It refutes `invalid_encoding_len` in section 19.

### N6. `resolve::Error::labels` and `assign::Error::labels` overflow at `offset = usize::MAX`

- Input: `resolve::Error::NotFound { position: 0, offset: usize::MAX }` with the subject
  `"/a"`; likewise `assign::Error::OutOfBounds` with the same position and offset.
- Expected: a label or no label, without a panic.
- Release: `attempt to add with overflow` at `resolve.rs:222` and `assign.rs:222` in the
  debug profile. In the release profile the sum wraps and the label is offset 0, length 1.
- Assessment: low severity. No resolution or assignment produces this offset; the variants
  are publicly constructible.

### N7. `ParseError::complete_offset` overflows on a hand-built error

- Input: `ParseError::InvalidEncoding { offset: usize::MAX, source: EncodingError {
  offset: 1, source: Tilde } }`.
- Expected: a value without a panic; the method takes no subject to validate against.
- Release: `attempt to add with overflow` at `pointer.rs:1319` in the debug profile;
  0 in the release profile.
- Assessment: low severity, same class as N6. `ParseError::labels` calls this method.

### N8. `EncodingError::labels` underflows at offset 0 on an empty subject

- Input: `EncodingError { offset: 0, source: Tilde }` with the subject `""`.
- Expected: a label inside the subject or no label, without a panic.
- Release: `attempt to subtract with overflow` at `token.rs:426` in the debug profile. In
  the release profile the label has offset `usize::MAX` and length 1.
- Assessment: low severity. `from_encoded` never reports `Tilde` at offset 0. The fields
  are public.

### Observations from this round that are not findings

- Range indexing requires the start to name an existing token. `"/a".get(1..1)` and
  `"".get(0..0)` are `None`, while `"/a".get(0..0)` and `"".get(..0)` are the root. This
  differs from slice indexing, but the crate's own tests in `pointer/slice.rs` assert it,
  so the specification adopts it.
- `strip_suffix` accepts the root suffix for every pointer, while `ends_with` rejects the
  root for a non-root pointer. The second is documented; the first follows from string
  suffix removal. `"/a".strip_suffix("")` is `Some("/a")` and `"/a".ends_with("")` is
  false.
- The derived order on `Pointer` is bytewise, not token-wise: `"/a-"` sorts before
  `"/a/b"`. By source inspection only.
- Assignment expands a missing path with a one-item array for the tokens `0` and `-` and
  an object for every other token, including `1`. After assigning at a path containing
  `-`, that path does not resolve. Both are the documented expansion rule.
- `PointerBuf::replace` returns `Option` but never `Ok(None)`.
- For an error on an empty last token, such as resolving `"/a/"` on `{"a": 1}`, the label
  is offset 2, length 0: it sits on the separator, not after it.
- `resolve::Error` has no `miette::Diagnostic` implementation, while `assign::Error`,
  `ParseError`, `EncodingError` and `ParseIndexError` have one. By source inspection.
- With `serde_json`'s `preserve_order` feature, `Map::remove` may reorder members. The
  crate does not select that feature; it is listed as an open correspondence obligation.

## Third round: diagnostic addresses

Added on 2026-11-28 while reviewing the tier 2–3 statements. A third scratchpad probe
printed `Diagnostic::url()` for all five implementations, in the debug and the release
profile, with the features `resolve` and `assign`. Both profiles printed the same five
strings. The docs.rs pages themselves were not fetched; the expected addresses follow
rustdoc's naming, `<module path>/<kind>.<Name>.html`.

| Type | Declared as | Release `url()` path after `jsonptr/0.8.2/` | Expected path |
| --- | --- | --- | --- |
| `ParseError` | `pub enum`, re-exported at the root | `jsonptr/struct.ParseError.html` | `jsonptr/enum.ParseError.html` |
| `EncodingError` | `pub struct`, re-exported at the root | `jsonptr/struct.EncodingError.html` | same |
| `index::ParseIndexError` | `pub enum`, not re-exported | `jsonptr/enum.ParseIndexError.html` | `jsonptr/index/enum.ParseIndexError.html` |
| `assign::Error` | `pub enum` | `jsonptr/assign/enum.Error.html` | same |
| `resolve::Error` | `pub enum` | `jsonptr/assign/enum.Error.html` | `jsonptr/resolve/enum.Error.html` (N3) |

### N9. `ParseIndexError::url` omits the `index` module

- Cause: `index.rs:362` uses `diagnostic_url!(enum ParseIndexError)`, the form for a type
  at the crate root. `lib.rs` declares `pub mod index;` and re-exports nothing from it, so
  the type's only public path is `jsonptr::index::ParseIndexError`.
- Assessment: a real defect of the same kind as N3. The implementation agent noticed it
  first. Section 19 of the specification already requires the address of the error type,
  so the contract is refuted for this type as well.

### N10. `ParseError::url` names a struct page for an enum

- Cause: `pointer.rs:1214` uses `diagnostic_url!(struct ParseError)`, but `ParseError` is
  declared `pub enum` at `pointer.rs:1171`. rustdoc names the page `enum.ParseError.html`.
- Assessment: a real defect of the same kind. Section 19 is refuted for this type too.
  Three of the five addresses are therefore wrong: `ParseError`, `ParseIndexError` and
  `resolve::Error`.
