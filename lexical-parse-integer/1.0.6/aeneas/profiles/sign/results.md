# Verification results

The final managed run `sign-ojzz29eb` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/sign-ojzz29eb`.

## Scope and boundaries

The adapted sign helper covers all optional bytes and flag combinations, with the premise that an accepted sign can advance the cursor within usize. Errors and no sign leave the cursor unchanged.

The harness accepts flags and cursor explicitly; caller flag computation and formal release equivalence are outside this scope.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked --offline --manifest-path verification/sign-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
