# JSONPTR-002 — Pointer::get overflows the maximum excluded start bound

- Crate/version `jsonptr/0.8.2`
- Component and kind — release implementation, implementation bug
- Confidence and resolution — reproduced at pinned inputs, open
- First observed and last reproduced — 2026-11-27
- Upstream report — not reported
- Upstream fix — not checked
- Pinned inputs, exact commands and raw logs — [shared native evidence](README.md#shared-native-evidence)
- Reproducer — [`excluded_maximum_bound_overflows`](../native/src/main.rs)
- Local upstream draft — [issue body](issue-drafts/JSONPTR-002.md)

`Pointer::get` documents `None` for out-of-bounds indices. The supported
`(Bound<usize>, Bound<usize>)` index with start `Excluded(usize::MAX)`
cannot select any token index above that bound. The call should return `None`.

On `"/one/two"`, each of the three end-bound forms panics in debug with
`attempt to add with overflow`. In release, end bounds `Included(0)`,
`Excluded(1)` and `Unbounded` produce `Some("/one")`, `Some("/one")` and
`Some("/one/two")`, respectively. The ordinary range `usize::MAX..`
returns `None`, and `(Excluded(0), Unbounded)` selects `"/two"`.

The three branches share the same unchecked `start + 1` in
`.work/source/src/pointer/slice.rs:201–203`. Check the addition and return
`None` on overflow. Re-run all three end-bound cases to check both profiles.
An unconditional out-of-bounds contract covering this input is false for the
release's tuple implementation.
