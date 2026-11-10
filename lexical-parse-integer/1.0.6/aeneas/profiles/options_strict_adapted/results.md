# Verification results

The final managed run `options_strict_adapted-25t1ib4w` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/options_strict_adapted-25t1ib4w`.

## Scope and boundaries

The adapted strict builder returns the builder state, and adapted SMALL_NUMBERS and LARGE_NUMBERS have the specified Boolean states. The release build is separately proved to return Ok for both states.

The copied strict source replaces the unreachable error-arm panic with build_unchecked. The source checker verifies this replacement; formal Rust-to-Rust equivalence is not established.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked --offline --manifest-path verification/options-strict-harness/Cargo.toml --features power-of-two --test strict_compare`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
