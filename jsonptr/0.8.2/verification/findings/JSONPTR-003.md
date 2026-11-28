# JSONPTR-003 — A final bare tilde produces an out-of-bounds diagnostic span

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27
- Upstream report — not reported
- Upstream fix — not checked
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`terminal_tilde_diagnostic_extends_past_input`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-003.md)

Parsing `"/~"` correctly fails. For that error and its original subject,
`complete_offset()` is 1, the byte offset of the tilde. Only one byte of
input remains, so `invalid_encoding_len` should report 1. It instead
reports 2, producing the span `1..3` for a two-byte input. Other confirmed
cases are `"/a~"`, `"/a/~"` and `"/é/~"`. An invalid escape with an ASCII
successor, `"/a~2"`, correctly gives byte offset 2 and length 2.

The released `invalid_encoding_len` compares the offset of the token's
separator with the subject length rather than the complete offset of the
tilde (`.work/source/src/pointer.rs:1196–1207`). Source inspection shows that
`Diagnostic::labels` combines the complete offset and this length, so the
defect affects the span supplied to diagnostic consumers. The native harness
checks these two public accessors. Rendering through optional miette
integration has not been tested.

Calculate the remaining input length from the complete offset and handle a
terminal tilde as a one-byte span. The regression should retain both the
terminal tilde and the nonterminal invalid ASCII escape cases. This is a
diagnostic length defect on the original subject and leaves the tested
parser's rejection decision intact.
