# JSONPTR-006 — Diagnostic::url names the wrong docs.rs page for three error types

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27 for `resolve::Error`, 2026-11-28 for the other two; last reproduced 2026-11-28
- Upstream report — not reported; no matching issue found
- Upstream fix — not fixed at default-branch commit `41a813bd4e7e89a0251bf2fc559c7159933a1066` by source inspection; not tested there
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`diagnostic_urls_name_wrong_pages`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-006.md)

`Diagnostic::url` is documented as "The docs.rs URL for this error"
(`.work/source/src/diagnostic.rs:17`). The expected address follows rustdoc's
page naming, `<module path>/<kind>.<Name>.html`, applied to each type's public
path in `.work/source/src/lib.rs`. `pointer` and `token` are private modules
whose types are re-exported at the crate root, so rustdoc documents
`ParseError` and `EncodingError` at the root. `index`, `assign` and `resolve`
are public modules, and nothing from `index` is re-exported. The docs.rs
pages were not fetched. The expected paths come from these naming rules,
not from retrieving the pages. On 2026-11-28 the independent reviewer ran a
local `cargo +1.91.0 doc --no-deps -p jsonptr` with default features. It
generated `enum.ParseError.html`, `index/enum.ParseIndexError.html`,
`resolve/enum.Error.html`, `assign/enum.Error.html` and
`struct.EncodingError.html`, and generated neither `struct.ParseError.html`
nor a root-level `enum.ParseIndexError.html`.

| Type | Declaration | `url()` path after `https://docs.rs/jsonptr/0.8.2/jsonptr/` | Expected |
| --- | --- | --- | --- |
| `resolve::Error` | `pub enum`, `resolve.rs:88` | `assign/enum.Error.html` | `resolve/enum.Error.html` |
| `index::ParseIndexError` | `pub enum`, `index.rs:282` | `enum.ParseIndexError.html` | `index/enum.ParseIndexError.html` |
| `ParseError` | `pub enum`, `pointer.rs:1171` | `struct.ParseError.html` | `enum.ParseError.html` |
| `assign::Error` (control) | `pub enum`, `assign.rs:135` | `assign/enum.Error.html` | same |
| `EncodingError` (control) | `pub struct`, `token.rs:398` | `struct.EncodingError.html` | same |

The native test asserts these five strings in debug and release.

Each wrong address comes from the argument to the private `diagnostic_url!`
macro. `resolve.rs:216` passes `enum assign::Error`, copied from
`assign.rs:215`. `index.rs:362` passes `enum ParseIndexError`, the root-level
form, without the `index` module. `pointer.rs:1214` passes
`struct ParseError` for an enum. By source inspection, `Report<T>` returns
`T::url()` from its `miette::Diagnostic::url`, and `assign::Error` has its
own miette `url` that forwards to the same function, so miette output
carries the same addresses.

Fix the three macro arguments to `enum resolve::Error`,
`enum index::ParseIndexError` and `enum ParseError`. A regression test can
compare all five strings. Checking that the pages exist on docs.rs needs
network access and was not done here.
