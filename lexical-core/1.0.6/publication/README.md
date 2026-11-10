# Publication package: conditional facade laws

This package is an explicit verification fork named `lexical-core` 1.0.6 for proofs.rs recording. Its library target selects the same physical [adapted facade source](../verification/facade/src/lib.rs) used by the local facade proof. The six release function definitions are unchanged, but unused supertrait and associated-option bounds are erased. There are no concrete numeric implementations in this library. Neither release-trait equivalence nor integer/float algorithm correctness follows from its claims.

[Facade.lean](proofs/Facade.lean) was freshly extracted from this manifest with crate library name `lexical_core`. [Proofs.lean](proofs/Proofs.lean) proves six forwarding equalities and six conditional total-success transfers against that new model. Each public claim requires the supplied dictionary call to succeed and satisfy the chosen output relation. Writer equalities preserve the complete returned-slice/backward-function tuple. Only the six conditional theorems are mapped to APIs; numerical compact-writer evidence and findings remain separately scoped supplemental material.

`check-source.py` checks the selected source identity and six exact release function definitions. `setup.py` restores and independently checks a checksum-pinned upstream archive as correspondence provenance. This archive is **not** the selected fork library, and its inventory check does not establish release equivalence. The selected fork is committed Rust source outside this package but inside the same repository. Cargo metadata and the recorder discover that exact source file.

The proof package uses ordinary module paths and an official Git Aeneas dependency pinned to `be86ab0f1989d04944292b345b24c435be3ad10a`, with Lean 4.35.0. No Aeneas/Charon source or generated Lean is edited. The optional preparation hook only restores provenance and seeds checked Git dependency caches; the CLI still runs standard Lake and its own theorem/axiom audit.

## Recording

Use a clean, pushed source checkout. The current development checkout has unrelated ancestor Cargo configuration; the publication lock was generated from a temporary execution directory outside those ancestors. The clean publication checkout must likewise use its own committed configuration, not an inherited Creusot environment. Rust 1.94.1 was used for Cargo metadata; extraction used nightly-2026-09-17.

For the local dependency donor prepared in this session, set these variables before entering the clean publication checkout:

```sh
export LEXICAL_CORE_PUBLICATION_LAKE_CACHE=/Users/mwaga/crate-proofs/lexical-core/1.0.6/publication/proofs/.lake/packages
export CARGO_HOME=/Users/mwaga/crate-proofs/lexical-core/1.0.6/.work/cargo-home
export RUSTUP_TOOLCHAIN=1.94.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
```

Run the pinned CLI from that checkout's `lexical-core/1.0.6/publication/proofs` directory:

```sh
/Users/mwaga/crate-proofs/.work/tools/b2f666ef0902d4b779bbbb0f81e7b9b90d1fe3f630dda0dfe475b7e35c1acd4e/cargo-proofs/bin/cargo-proofs run --manifest-path ../Cargo.toml -- lake build
```

The donor path is a performance input, not proof evidence: every package must have the exact locked Git revision, origin and clean tracked source before reuse. Without a donor, ordinary Lake obtains its pinned dependencies. Standard builds/audits remain mandatory. The archive/source preparation script emits no successful formal result and embeds no setup logs in SARIF.

After a successful CLI recording, the authorized publisher can validate and publish that specific recorded run. The existing local profile acceptance is separate from CLI recording, catalogue validation and service publication.
