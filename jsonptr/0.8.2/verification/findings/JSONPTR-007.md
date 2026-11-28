# JSONPTR-007 — EncodingError::offset documentation names the tilde, but tilde errors hold the next offset

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation (rustdoc on a public field), documentation mismatch
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27 and 2026-11-28
- Upstream report — not reported; no matching issue found. [chanced/jsonptr#128](https://github.com/chanced/jsonptr/issues/128) (closed) concerns accepting `"~~0"`, not this field's documentation
- Upstream fix — the same documentation is present at default-branch commit `41a813bd4e7e89a0251bf2fc559c7159933a1066` by source inspection
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`encoding_error_offset_is_after_tilde`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-007.md)

The public field `EncodingError::offset` is documented as "offset of the
erroneous `~` from within the `Token`" (`.work/source/src/token.rs:399`). For
`Token::from_encoded("a~b")` that reading gives 1.

For `InvalidEncoding::Tilde` the field holds the offset of the byte after the
tilde. For a final tilde it holds the token length. Observed in debug and
release:

| `Token::from_encoded` input | Tilde at | `offset` |
| --- | --- | --- |
| `"a~b"` | 1 | 2 |
| `"~"` | 0 | 1 |
| `"~~"` | 0 | 1 |
| `"invalid~tilde"` | 7 | 8 |

For `InvalidEncoding::Slash` the field is the offset of the slash itself;
`"a/b"` gives 1.

This record classifies the documentation, not the value, as wrong. The value
is used consistently. `from_encoded` reports the offset of the offending byte
after the tilde, or `inner.len()` at the end (`token.rs:80–108`).
`EncodingError::labels` puts "must be 0 or 1" at that offset and "incomplete
escape sequence" at that offset minus one (`token.rs:422–433`). `"a~b"`
gives the label at offset 2, length 1. `Pointer::parse` stores the same
number measured from the separator slash. `"/a~b"` gives `pointer_offset()`
0, `source_offset()` 2 and `complete_offset()` 2, which is the tilde's
offset in the pointer. The release's own unit tests assert offset 2 for
`"a~a"` and `"a~"`, and offset 1 for `"~~0"` (`token.rs:521–615`). The
`ParseError::source_offset` example also documents 8 for
`"/foo/invalid~tilde/invalid"`, consistent with this value.

The proposed fix is a documentation change describing both variants. For
`Tilde`, the field is the byte offset immediately after the `~`, which is
the token length for a final `~`. For `Slash`, it is the offset of the
`/`. Changing the value instead would also require changing `labels`, the
parser's `source_offset` and the tests. No regression code is needed for a
documentation fix. The native test pins the current values.
