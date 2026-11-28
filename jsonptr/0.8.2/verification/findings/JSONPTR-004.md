# JSONPTR-004 — ParseIndexError labels panic for an all-zero index token

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27 and 2026-11-28
- Upstream report — not reported; no matching issue found
- Upstream fix — not fixed at default-branch commit `41a813bd4e7e89a0251bf2fc559c7159933a1066` by source inspection; not tested there
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`all_zero_index_label_panics`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-004.md)

`Index::from_str` and the `TryFrom` conversions return
`ParseIndexError::LeadingZeros` for any token that starts with `'0'` and is
not `"0"`. For `"00"` and `"000"` this is the correct rejection under the
RFC 6901 array-index grammar. `Diagnostic::labels` for that error, given the
token as its subject, should return one "leading zeros" label inside the
token. The crate's own test expects offset 0 and length 5 for `"000001"`.
Which length is right for an all-zero token (all zeros, or all but the
last) is left open. A panic is not.

For `"00"` and `"000"`, `labels` panics with `starts with zeros` at
`.work/source/src/index.rs:376` in debug and release. The controls `"01"`,
`"0a"` and `"000001"` return offset 0 with lengths 1, 1 and 5. The subject
is the `StringOrToken` that `Diagnose::diagnose` builds from the same
string, so the error and subject match.

The label length is
`subject.chars().position(|c| c != '0').expect("starts with zeros")`
(`index.rs:373–376`). It assumes a character other than `'0'` follows the
zeros, which an all-zero token lacks. By source inspection, any subject
without such a character also panics with a hand-built `LeadingZeros`,
including the empty string.

The `miette` integration reaches the same code. `Report<T>` implements
`miette::Diagnostic::labels` by calling `T::labels`
(`.work/source/src/diagnostic.rs:131–133`). A scratch program with the
`miette` feature and miette 7.4.0 printed
`miette::Report::new(report)` for each input. For `"00"` and `"000"` it wrote
the error message and then panicked at `index.rs:376`, exiting 101 in debug
and release. `"01"` rendered a "leading zeros" label and exited 0. That program
resolved miette and its dependencies offline from the local registry cache,
so its own lockfile differs from the harness. It is not checked in. Its
source, lockfile and log are listed in the
[shared native evidence](README.md#miette-rendering-probe).

Resolution does not call this code. `resolve::Error::labels` and
`assign::Error::labels` label the token without asking the nested
`ParseIndexError` for its own labels. Callers reach the panic by calling `labels` on a
`ParseIndexError::LeadingZeros`, directly or on the parts of a report from
`Index::try_from(..).diagnose(..)`, or by miette rendering of such a report.

A fix can use the position of the first non-zero character when one exists
and otherwise choose a defined length within the token. The regression
should retain `"01"`, `"0a"` and `"000001"`, and add `"00"`, `"000"` and the
miette path.
