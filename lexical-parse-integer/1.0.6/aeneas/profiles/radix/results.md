# Verification results

The final managed run `radix-v49p8hmq` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/radix-v49p8hmq`.

## Scope and boundaries

Four- and eight-byte recognition and positional decoding for radices 2 through 10. Recognition covers every packed word; decoding requires all bytes to be digits in the selected radix.

The explicit radix replaces the release FORMAT lookup; source comparison checks that replacement, not formal Rust-to-Rust equivalence.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked`; `cargo test --locked --manifest-path verification/radix-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
