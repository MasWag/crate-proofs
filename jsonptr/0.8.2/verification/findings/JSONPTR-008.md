# JSONPTR-008 — Diagnostic helpers overflow on hand-built errors or mismatched subjects

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug (low severity)
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27 and 2026-11-28
- Upstream report — not reported; no matching issue found
- Upstream fix — not fixed at default-branch commit `41a813bd4e7e89a0251bf2fc559c7159933a1066` by source inspection; not tested there
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`diagnostic_helpers_overflow_on_hand_built_errors`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-008.md)
- Related — [JSONPTR-003](JSONPTR-003.md) is a different defect in `invalid_encoding_len` on a matching subject

`ParseError`, `EncodingError`, `resolve::Error` and `assign::Error` have
public variants or fields, so callers can build any field values. The
diagnostic helpers also accept any subject. No documentation states a
precondition on the fields or the subject, and none documents a panic.
Returning without panicking on every accepted input is a stronger desired
contract, not a documented guarantee. The release-mode results are
nevertheless not meaningful spans (for example a label at offset
`usize::MAX`). Five calls instead reach unchecked `usize` arithmetic.
Default debug builds panic with an overflow, and default release builds wrap:

| Call | Source line | Debug | Release |
| --- | --- | --- | --- |
| `ParseError::InvalidEncoding { offset: 0, source: EncodingError { offset: 1, source: Tilde } }.invalid_encoding_len("")` | `pointer.rs:1200`, `subject.len() - 1` | `attempt to subtract with overflow` | 2 |
| `resolve::Error::NotFound { position: 0, offset: usize::MAX }.labels(&"/a")` | `resolve.rs:222`, `self.offset() + 1` | `attempt to add with overflow` | `Label("not found in value", 0, 1)` |
| `assign::Error::OutOfBounds { position: 0, offset: usize::MAX, source: OutOfBoundsError { length: 0, index: 1 } }.labels(&"/a")` | `assign.rs:222`, `self.offset() + 1` | `attempt to add with overflow` | `Label("1 is out of bounds (len: 0)", 0, 1)` |
| `ParseError::InvalidEncoding { offset: usize::MAX, source: EncodingError { offset: 1, source: Tilde } }.complete_offset()` | `pointer.rs:1319`, `source_offset() + pointer_offset()` | `attempt to add with overflow` | 0 |
| `EncodingError { offset: 0, source: Tilde }.labels(&String::new())` | `token.rs:426`, `self.offset - 1` | `attempt to subtract with overflow` | `Label("incomplete escape sequence", usize::MAX, 1)` |

The `&"/a"` subject is `PointerBuf::parse("/a")`. The native test checks the
exact panic message in debug and the exact wrapped result in release. The
controls `Pointer::parse("/a~").complete_offset()` (2) and
`resolve::Error::NotFound { position: 0, offset: 0 }.labels(&"/a")`
(offset 1, length 1) are unaffected.

No parse, resolve or assign operation in the release was found to produce
these values. `from_encoded` never reports `Tilde` at offset 0. The parser's
offsets are bounded by the input length. Resolution offsets are offsets into
an existing pointer. `invalid_encoding_len("")` needs an error that did not
come from parsing `""`. The defects therefore affect code that builds or modifies
errors by hand, or pairs an error with a different subject. `ParseError::labels` calls both `complete_offset` and
`invalid_encoding_len`, so it inherits these cases. That severity
assessment comes from source review. The overflow behaviour itself is
reproduced.

Use checked or saturating arithmetic, or return `None` from `labels` when
the offset does not fit the subject. Alternatively, document the field and
subject preconditions. The regression should keep the five calls above, run
in debug and release, plus the two controls.
