# Verification results

The final managed run `caller-i_t5f06e` passed locally on 2026-11-06 on
`aarch64-apple-darwin`. Its recorded input fingerprints matched and the
theorem inventory and mappings passed audit. See [evidence/summary.json](evidence/summary.json)
for run identities and evidence; the local run is `.work/runs/caller-i_t5f06e`.

## Scope and boundaries

Safe decimal four- and eight-byte caller adaptations return the positional value exactly for a valid block and advance by its width; short or invalid blocks return no value and leave the cursor unchanged. The cursor plus remaining slice length must fit usize.

The release uses an iterator and unaligned pointer read. Equivalence to those original callers is not formally proved.

The proof relies on the pinned Rust-to-Lean translation, Aeneas models and Lean
kernel. See [proofs.toml](proofs.toml) for exact mappings, premises and trust
boundaries.

## Native checks

The run also passed `cargo test --locked --offline --manifest-path verification/caller-harness/Cargo.toml`. Native tests are separate evidence and do not
establish the formal contracts or release equivalence.
