# JSONPTR-005 — The InvalidCharacter index label runs past the token or splits a character

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27 and 2026-11-28
- Upstream report — not reported; no matching issue found
- Upstream fix — not fixed at default-branch commit `41a813bd4e7e89a0251bf2fc559c7159933a1066` by source inspection; not tested there
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`invalid_character_label_exceeds_subject`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-005.md)

For `ParseIndexError::InvalidCharacter`, `Diagnostic::labels` returns one
"invalid character(s)" label. It starts at the error's offset, which is the
first non-digit. The label should cover the following run of non-digits up to
the next ASCII digit or the end of the token. Its length should be in bytes,
because every other label in the crate uses byte offsets into the subject.
miette's `LabeledSpan`, which `Label` converts into, also uses byte offsets.
The `Label` documentation does not state the unit. For `"1abc"` the expected
label is offset 1, length 3. The independent minimum is that offset plus
length does not exceed the subject's byte length and ends on a character
boundary; all four defective rows violate it. The exact expected lengths
follow the crate's own test `error_from_invalid_chars` (`index.rs:549–573`,
`"bar"` gives 0, 3) and the release code's stop condition at the next ASCII
digit.

Observed labels with the matching subject, identical in debug and release:

| Subject | Bytes | Label (offset, length) | Expected |
| --- | --- | --- | --- |
| `"1abc"` | 4 | 1, 4 (ends at 5) | 1, 3 |
| `"1-"` | 2 | 1, 2 (ends at 3) | 1, 1 |
| `"1é"` | 3 | 1, 3 (ends at 4) | 1, 2 |
| `"aé1"` | 4 | 0, 2 (ends inside `é`) | 0, 3 |
| `"bar"` (control) | 3 | 0, 3 | 0, 3 |
| `"1a2"` (control) | 3 | 1, 1 | 1, 1 |

The length is computed at `.work/source/src/index.rs:381–385` as
`subject.chars().skip(err.offset).position(|c| c.is_ascii_digit())
.unwrap_or(subject.len())`. Two defects share these lines. With no later
digit, the fallback is the whole subject length rather than the length from
the offset, so the span ends past the subject whenever the offset is
nonzero. When a digit does follow, `position` counts characters, so a
non-ASCII character in the run makes the length too short in bytes. The
offset is unaffected. `InvalidCharacterError::offset` is documented in
characters, but only ASCII digits precede it, so it equals the byte offset.

With the `miette` feature and miette 7.4.0, a scratch program printed the
`miette::Report` for `"1abc"` as a multi-line span marker over the token,
without the "invalid character(s)" text. It exited 0 in both profiles.
`"aé1"` and `"bar"` rendered the label text. This is a single rendering
observation. See the [miette rendering probe](README.md#miette-rendering-probe).

Compute the length from the byte offset as the byte distance to the next
ASCII digit or to the end of the subject. The regression should cover the
four defective rows and both controls.
