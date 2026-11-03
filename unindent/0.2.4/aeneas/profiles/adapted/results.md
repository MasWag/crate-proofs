# Adapted scanner results

Managed run `adapted-xs1kvasj` passed on `x86_64-unknown-linux-gnu`: exact generated
model comparison, standard Lake build, the two named scanner theorem audits,
deterministic release-derived source checks, and identical before/after input
fingerprints. These are results for that run's original inputs.

`unindent.Proofs.line_end_total_exact` proves that the generated LF scanner
succeeds at the first LF at or after a valid starting index, or at the input end
when none exists. `unindent.Proofs.leading_end_spec` proves total success at the
first non-SPACE/TAB byte in a valid interval, or its endpoint. Their dependencies
contain only `propext`, `Classical.choice`, and `Quot.sound`. Both are private
support theorems; there are no public API mappings in this profile.

The implementation is derived from the locked release by
`patches/explicit-index.patch`; `scripts/prepare-source.py` checks its exact
bytes. It deliberately replaces the iterator pipeline with explicit indexed
scanners. Aeneas and Charon remain unchanged. The full byte core extracts, but
neither its complete functional behavior nor formal equivalence to the release
has been proved. This profile does not verify the release's public byte or string
APIs.

The separate native comparison checked all 960,800 inputs of lengths 0 through 7
over SPACE, TAB, LF, CR, A, NUL, and FF without a mismatch. Native finite agreement
is not a proof of equivalence for arbitrary inputs.

Run `scripts/verify.sh --profile adapted --offline` from the version root after
setup and dependency caching. Raw runs are kept in ignored `.work/runs/`.
Compact evidence is stored in `evidence/`; the complete archive is retained in
version-local `.work/evidence-archives` and is not publicly downloadable. A subsequent tool/configuration change requires a fresh run.
