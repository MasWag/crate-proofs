# Experimental byte scanner contracts

Specification responsibility: the independent correctness-review agent, separate
from proof implementation. This follow-up defines and reviews the narrow scanner
contracts; it does not replace the default profile's full public byte semantics.

## Subject and source correspondence

This profile applies `patches/explicit-index.patch` to the locked release's
`src/unindent.rs`, placing the result in an independent experimental workspace
at `.work/adapted`. The preparation script checks exact resulting source bytes.
The patch introduces `line_end_index`, `leading_end_index`, `common_margin`, and
`append_range` and replaces the iterator-based byte algorithm with explicit
index loops. These scanner functions are new adapted-source helpers, not
unchanged functions from the release. Aeneas and Charon remain unmodified.

The generated `CoreAdapted.lean` includes the adapted byte algorithm, but this
profile proves only the two scanners. Formal equivalence of the patched byte
algorithm to the release is unproved. Finite native comparisons, including all
960,800 byte strings of lengths zero through seven over SPACE, TAB, LF, CR, A,
NUL and FF, are separate observations and do not prove equivalence.

## Independent scanner semantics

Let `s` be any representable byte slice, `n` its length, and let positions be
natural numbers represented by Rust `usize`. SPACE is 32, TAB is 9, and LF is 10.
No byte-content restrictions apply.

For `0 ≤ start ≤ n`, `line_end_index(s, start)` must terminate successfully and
return the least position `j` in `[start, n)` for which `s[j] = LF`, or `n` if
there is no such position. Equivalently, the result lies in `[start, n]`, is
at the slice end or contains LF, and every earlier position from `start` is
not LF. In particular, starting at `n` returns `n` without indexing the slice.

For `0 ≤ start ≤ finish ≤ n`, `leading_end_index(s, start, finish)` must terminate
successfully and return the least position `j` in `[start, finish)` whose byte
is neither SPACE nor TAB, or `finish` if every byte in that interval is SPACE
or TAB. Equivalently, the result lies in `[start, finish]`, is at `finish` or
contains a non-whitespace byte, and every earlier byte from `start` is SPACE
or TAB. An empty interval returns `finish`. LF, CR, NUL, and bytes above ASCII
are all non-whitespace for this scanner.

The bounds are caller obligations for these internal indexed helpers, not
restrictions on the full public byte input domain. Composition into the byte
algorithm must prove them at each actual call. Native allocation resources
are outside these pure scanner contracts.

## Proof review and outstanding coverage

The maintained proofs use the decreasing number of unscanned bytes and invariants
preserving the scanned prefix property. Bounds on slice length and positions
justify index access and counter increment. The postconditions characterize the
least qualifying position without assuming a prior scanner result. The current
`line_end_total_exact` states existence of a successful exact result explicitly;
`leading_end_spec` uses Aeneas's total-success weakest precondition with the
specified first-non-whitespace postcondition. These are appropriate support
contracts with no assumption of public algorithm correctness.

Registration for a fresh managed scanner audit is appropriate. Acceptance still
requires fresh extraction comparison, Lean build, transitive axiom audit, and
stable input fingerprints. No public API should be mapped to either helper.
The margin minimum, output assembly, full adapted byte transformation, release
correspondence, all public original implementations, and UTF-8 preservation
remain unproved by this profile.
