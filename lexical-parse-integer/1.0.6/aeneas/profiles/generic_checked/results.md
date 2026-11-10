# Verification results

The final managed run `generic_checked-jqglkzgd` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/generic_checked-jqglkzgd`.

## Scope and boundaries

Complete-mode checked scalar helper adaptations cover all integer widths and radices 2 through 36. Cursor plus remaining length must fit usize; signed positive and negative entries must be nonnegative and nonpositive respectively.

The outlined slice-based bodies are source checked adaptations; full front ends and formal Rust-to-Rust equivalence are outside this profile.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked --offline --manifest-path verification/generic-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
