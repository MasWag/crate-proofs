# JSONPTR-001 — Pointer::strip_prefix can return a malformed Pointer

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug
- Confidence and resolution — reproduced at pinned inputs, open in 0.8.2
- First observed and last reproduced — 2026-11-27
- Upstream report — [chanced/jsonptr#131](https://github.com/chanced/jsonptr/issues/131) describes the same cause on 0.7.1
- Upstream fix — open pull request [chanced/jsonptr#132](https://github.com/chanced/jsonptr/pull/132) (checked 2026-11-28, unmerged and unreleased) makes `strip_prefix` return `None` unless the remainder is empty or starts with `/`; reviewed from its diff only, not built or tested here
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`strip_prefix_requires_a_token_boundary`](../native/src/main.rs)
- Local upstream follow-up — [draft](issue-drafts/JSONPTR-001.md)

Both arguments are valid pointers. `"/ab"` has one token, `ab`, so it has no
initial token `a` to remove. `starts_with` rejects the prefix, consistent with
the token boundaries in [RFC 6901 §3](https://www.rfc-editor.org/rfc/rfc6901#section-3).

`strip_prefix` returns `Some` containing the string `"b"`, which `Pointer::parse`
rejects. The same defect gives `"~0"` when stripping `"/"` from `"/~0"`.
When the malformed remainder is `"é"`, `front()` panics on a UTF-8 boundary
check in both profiles. The controls `"/a/東京"` minus `"/a"` and `"/a"` minus
itself give `"/東京"` and the root pointer, respectively.

In `.work/source/src/pointer.rs:287–293`, the raw string prefix test permits
a match inside a token, then wraps the remainder without validation. Require
an empty remainder or a remainder beginning with a separator slash before
constructing the result. The regression should also preserve valid whole-token
matches, including equality and the root prefix. This is native evidence of
failure for valid arguments and shows that an unconditional token-prefix
contract is false for this release.
