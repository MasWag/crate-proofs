# Default profile acceptance

The managed run `default-53rdjz7x` passed on `aarch64-apple-darwin`. It checked the derived source, regenerated model, and matching before/after input fingerprints, then passed the named theorem and transitive axiom audit: 12 public raw-method contracts and 26 supporting theorems, 38 total. The API mappings and exact preconditions are in [proofs.toml](proofs.toml); the contracts and their domains are explained in [SPECIFICATION.md](../../../SPECIFICATION.md). The audit permits `propext`, `Classical.choice`, and `Quot.sound`. This is a proof of the selected translated harness under the recorded models, not a formal equivalence proof to the published source.

From `block-padding/0.4.2`, after preparing the pinned tools, the final run used:

```sh
env -u BASH_ENV -u ENV -u CPPFLAGS -u LDFLAGS bash scripts/verify.sh --offline
```

The Charon log records a failed Miri sysroot setup and fallback to rustc's default sysroot. Native debug and release runs separately passed one integration test and six doctests each. The expected-failure reproduction remains ignored in ordinary runs; it is not counted as a passing test of the expected behavior.

The verified harness expands two decoder iterator checks into index loops. Source correspondence was reviewed, but not formally proved. Typed array methods, detached padding, block-list unpadding, `PaddedData::unwrap`, generic array representation and dependency behavior, marker and formatting behavior, separate roundtrip composition laws, and behavior outside the stated raw domains remain unproved. The [coverage ledger](../../../RESULTS.md) and [extraction boundary record](../../../verification/extraction-boundaries/README.md) describe these limits. Native tests independently reproduce the three empty-input raw decoder panics described in the report finding.

The [evidence summary](evidence/summary.json) and [archive descriptor](evidence/archive.json) identify the original run and audit records. The archive is local-only in the workspace's ignored `.work/evidence-archives` store; it has no public URL. Packaging records the original run and does not rerun verification or produce a cargo-proofs recording result.
