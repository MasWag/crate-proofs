# Verification results

The final managed run `options-j84kfv7k` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/options-j84kfv7k`.

## Scope and boundaries

The directly extracted release options methods and STANDARD constant satisfy the state contracts in the profile report, including mutable setters and from_radix with power-of-two enabled.

The original build_strict and dependent constants are excluded because its panic branch encounters an Aeneas internal error; parser behavior is outside this scope.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked --offline --features power-of-two`; `cargo test --locked --offline --manifest-path verification/options-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
