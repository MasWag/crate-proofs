# Creusot investigation of unindent 0.2.4

This independent workspace targets the byte transformation, UTF-8 preservation
and concrete wrappers that remain unproved in the Aeneas report. The exact
contracts are in [the specification](verification/specification.md), with
[source and scope](verification/plan.md) and
[standard-library assumptions](verification/assumptions.md) recorded separately.
The [coverage ledger](verification/coverage.md),
[source correspondence](verification/source-correspondence.md), and
[independent contract review](verification/contract-review.md) define claim limits.
Run outcomes and evidence are recorded in [results](verification/results.md).
Reproduce with `bash scripts/verify.sh`; the runner requires a fresh integrated
run and independent root inventory audit.

Use `source scripts/env.sh` from this directory. The environment selects frozen
Creusot 0.13 and its compatible compiler, Why3 models and provers; it does not
activate the parent Aeneas environment. Tool installation locations are local
cache inputs, and their actual source/binary identities must be fingerprinted.

The immutable crates.io source and complete release inventory are pinned by
`../source.lock.json`. Runtime source here is an explicitly disclosed verification
adaptation. Proofs of this implementation do not alone establish formal equivalence
to the release's iterator pipeline. The original source's translation diagnostic,
finite native comparisons and proof logs remain in ignored `.work`.

The existing [Aeneas report](https://proofs.rs/report/20) retains its original
scope and source identity. New files in this track do not refresh that historical
acceptance. Creusot evidence and any subsequent publication are recorded separately.
