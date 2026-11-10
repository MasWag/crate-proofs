# Verification results

The final managed run `parser-r_8t62n3` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/parser-r_8t62n3`.

## Scope and boundaries

Complete and partial standard decimal u8 and i8 front-end adaptations cover arbitrary bytes, exact values, errors and partial counts. Scoped u8/u32/i32 loops and lexical-util digit conversion have the premises in the profile report.

The front ends and iterator are adapted; source checks and review do not establish formal equivalence to the release generic parser.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked`; `cargo test --locked --manifest-path verification/parser-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
