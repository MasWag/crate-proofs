# num-conv 0.2.2 Aeneas verification

Use only the managed Aeneas profile and unchanged checksum-pinned release source. Do not modify Aeneas. Scope all 180 concrete method contracts of Widen, deprecated Extend, and Truncate (wrapping, saturating, checked), including generic public dispatch. Native tests and formal proofs are separate. Specification design is assigned to Astra; implementation to Sol; primary independently reviews contracts, commands, evidence, and coverage. Unproved methods remain explicit in coverage. No publication.

The proof harness packages the unchanged checksum-locked release file as a local module and reexports its three public traits to preserve the prelude bindings. Keep all 180 wrappers as single direct public calls and check source correspondence with scripts/check-harness.py. This packaging is disclosed, not a formally proved Rust-to-Rust equivalence.
