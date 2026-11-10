# Verification results

The final managed run `default-szuh3wgu` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/default-szuh3wgu`.

## Scope and boundaries

Decimal four- and eight-byte recognition and positional decoding on specialized helper bodies. Recognition covers every packed word; decoding requires all bytes to be decimal digits.

The radix-10 source specialization is an adaptation; formal Rust-to-Rust equivalence and parser composition are not established.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked`; `cargo test --locked --manifest-path verification/harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.

The [historical accepted result](evidence/history/default-zbqap6ra-results.md) is preserved separately.
