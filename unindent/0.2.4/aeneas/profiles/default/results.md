# unindent 0.2.4 verification results

## Accepted scope

The unchanged crates.io release has one checked public delegation contract and
one checked private classifier. This is not a proof of either complete unindent
algorithm.

| Subject | Checked guarantee |
| --- | --- |
| Generic `Unindent for &T` | Exactly the underlying implementation's modeled result. If that implementation succeeds with a postcondition, the reference implementation succeeds with the same postcondition. |
| Private `count_spaces` | For every representable byte slice, succeeds with the first index whose byte is neither SPACE nor TAB, or `None` exactly when all bytes are SPACE/TAB. |

The theorem inventory contains the public total-success preservation theorem,
its exact-equality support theorem, and `UnindentProof.countSpaces_total_exact`.
Only the first theorem is mapped to a public API. The helper's transitive axioms
are `propext`, `Classical.choice`, and `Quot.sound`; there are no application
axioms or `sorryAx` dependencies.

## Evidence and identity

Managed run `default-5xfpzmm3` passed regeneration and byte comparison of both
maintained models, standard Lake build, the three named-theorem audits, and equal
before/after input fingerprints. Its native checks passed zero unit tests, two documentation tests, and the
minimal Cargo CRLF reproduction. Acceptance is tied to that run's original input
hashes, including the final recording configuration and report. Independent
Astra review rechecked the original artifacts and found no hash mismatches.

Raw execution records remain local under `.work/runs/`. The compact
evidence descriptor and summary identify the accepted final run under
`evidence/`. The complete archive is in version-local `.work/evidence-archives`;
it is local-only, with no public download URL.

Source identity is pinned in `source.lock.json`. The latest non-yanked version in
the Cargo registry index resolved on 2026-11-03 was 0.2.4. Its archive checksum is
`7264e107f553ccae879d21fbea1d6724ac785e8c3bfc762137959b5802826ef3`, independently
matched against the registry index. All nine restored release files match the
locked inventory. See `verification/source-identity.json` for registry and VCS
metadata.

The target is `x86_64-unknown-linux-gnu`, with the release's dependency and feature
surface. Aeneas revision `be86ab0f1989d04944292b345b24c435be3ad10a` and Charon
revision `08d7c9d50144bd84848212c24701253585e90d1f` are unchanged. Native Rust,
extraction Rust, Lean, OCaml packages, and the recording CLI are fixed by the
profile's tool lock. Source/tool checks reject unexpected modifications.

## Core algorithms and remaining proof work

Original `unindent_bytes` extraction fails at higher-ranked callback/function
pointer types in line splitting and the iterator pipeline; partial output also
reports unavailable iterator fields. It is excluded from accepted generated
models. Consequently neither `unindent_bytes`, `unindent`, concrete `str`,
`String`, or byte-slice trait implementations, nor UTF-8 closure is established.
These APIs remain explicit entries in the coverage ledger.

The separate `adapted` profile derives an explicit-index Rust implementation from
the immutable release using a retained patch. Its full byte core extracts with
unchanged Aeneas. Two scanner helpers have checked total contracts: the next LF
or endpoint, and the first non-SPACE/TAB within a valid interval. The complete
byte transformation and formal equivalence to the release remain unproved.
Comparing 960,800 inputs of lengths 0 through 7 over seven byte values found no
difference; this finite native comparison is not a correspondence theorem.
Read that profile's specification and results separately.

## Findings

The report contains one intended-behavior question: an interior empty CRLF line
forces a zero common margin, whereas the corresponding LF-only input is
unindented. The native reproduction calls the actual release API and succeeds
with the outputs shown in the finding. This is a documented observation and
specification question, not an asserted confirmed upstream bug.

The fixture is `verification/reproductions/crlf.rs`. Reproduce it with
`python3 scripts/reproduce-crlf.py` from the version root using the pinned native
Rust environment. This runs a minimal isolated Cargo harness against the restored
release. Findings have not been submitted upstream.

## Reproduction and publication

Run `scripts/setup.sh`, then `scripts/verify.sh --offline` after the required
sources, tool builds, and Lean dependencies have been cached. Profiles and
relevant tool hashes are recorded rather than inferred from executables on PATH.
`scripts/build-tools/cargo` can isolate tool builds from unrelated ancestor Cargo
configuration; it changes orchestration, not Aeneas or crate executable semantics.

Specification design used Astra; proof implementation used Sol; report prose used
Terra with independent Astra correctness review. The primary reviewed source
correspondence, commands, evidence and coverage claims.

CLI recording and proofs.rs publication are separate from this local acceptance.
The actual patched CLI's callable discovery resolved the configured
`<&T as unindent::Unindent>::unindent` mapping. This was a check of the intended
mapping, not a complete public API catalogue. The CLI patch passed 84 unit tests
and three integration tests (five additional tests intentionally ignored).

Recording preflight reached `Commit and push source changes before cargo proofs
run`, after discovery and preparation. The recording wrapper shares checked tool,
archive and Lean dependency caches with its detached checkout. `proof_modules`
requests a standard build of `Proofs.CountSpaces`; the public recorded theorem
mapping remains delegation only, and the private classifier's named-theorem audit
is separate local evidence. Publication remains pending until source-publication
prerequisites and the actual recording/service workflow succeed.
