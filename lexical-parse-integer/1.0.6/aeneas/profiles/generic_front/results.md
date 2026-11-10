# Verification results

The final managed run `generic_front-p9k_xq33` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/generic_front-p9k_xq33`.

## Scope and boundaries

Complete and partial front-end adaptations cover arbitrary bytes, all integer widths and radices 2 through 36, with standard no-format syntax and no_multi_digit=true. They establish exact values, errors and partial consumed counts. The usize and isize contracts require a 64-bit platform.

Safe slice/cursor, outlined macro and explicit-radix adaptations are source checked and reviewed. Formal Rust-to-Rust equivalence and the original generic parser and raw-memory paths remain unproved; custom syntax and multi-digit optimization are outside this scope.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked --offline --manifest-path verification/generic-parser-front-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
