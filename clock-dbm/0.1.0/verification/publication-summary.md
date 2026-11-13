# clock-dbm 0.1.0 verification

The unchanged Rust source and contracts from the crates.io release passed a
fresh Creusot 0.14.0 run on macOS arm64 on 2026-11-13: all 843 generated root
obligations closed. Independent Why3 reconstruction matched all 342 generated
Coma files and their sessions. The native build and 173 tests passed; six timing
benchmarks were ignored. All 21 upstream negative controls were rejected at
their expected targets. These counts are not public API counts.

The source archive SHA-256 is
`495398a8c1006f5c27c917ead62121ddd44392594ddbbb960e50b3af8d15664a`.
This publication snapshot contains the release Rust source, Cargo manifest and
lockfile, models, documentation, proof scripts and report. CI workflows and
local environment inventories are intentionally not part of this snapshot.
No Rust code or contracts were changed. Adding `proofs.toml` is report metadata.

Read the release's `verification/PROOF_STATUS.md` for the exact mathematical
contracts, trusted Rc specifications, exclusions and tool installation. Its
historical run table is distinct from the fresh run summarized here.

For service recording, activate the release's `verification/scripts/env.sh`,
call `use_pinned_rust`, and run from its package directory:

```sh
cargo proofs run -- cargo creusot --no-cache --erasure-check=error
```

The installed cargo-proofs 0.4.1 rejects nested `--` Cargo options, so this
recording command omits `-- --locked`. The recorder resolves locked metadata
and rejects changes to tracked inputs, including Cargo.lock. The separate full
gate used the upstream `-- --locked` command. Keep the same checkout path for
recording and publishing because the recorder keys local state by manifest path.

The public report's individual API claims are those mapped by the recorder;
the local full proof also covers supporting lemmas and trait obligations.
SharedDbm is verified relative to the stated Rc model. Hashing, formatting,
allocation failure, universal termination, ExtraM idempotence and automaton-level
reachability are outside the guarantees.
