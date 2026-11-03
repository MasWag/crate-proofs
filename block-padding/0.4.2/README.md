# block-padding 0.4.2 verification

This workspace investigates the crates.io `block-padding` 0.4.2 release. The pinned crate archive has SHA-256 `710f1dd022ef4e93f8a438b4ba958de7f64308434fa6a87104481645cc30068b`; individual source hashes are in [source.lock.json](source.lock.json). The specifications and intended boundaries are in [SPECIFICATION.md](SPECIFICATION.md). [RESULTS.md](RESULTS.md) tracks proof scope and native observations separately. The managed default-profile verification and named theorem audit passed; see the local run linked from RESULTS. A specification or extracted file alone is not a completed proof.

The local native test `tests/empty_unpad.rs` checks the observed empty-input behavior. `tests/representative_failure.rs` is intentionally ignored in normal test runs; its assertion demonstrates the discrepancy when explicitly run. The Aeneas report is published as [proofs.rs report 15](https://proofs.rs/report/15). No upstream issue has been filed. A separate [Kani workspace](kani/RESULTS.md) records bounded concrete-instance checks.

The verification harness replaces two decoder iterator checks with explicit index loops. `scripts/prepare-adaptation.py --check` checks the derived source against the pinned release; source review supports correspondence, but formal equivalence has not been proved. Aeneas and Charon remain unpatched.

From this version directory, activate and run the managed profile:

```sh
source scripts/env.sh
scripts/setup.sh --offline
scripts/verify.sh --offline
```

Setup requires the pinned inputs to have been installed already for offline use. Native tests and formal verification are separate.
