# jsonptr 0.8.2

This workspace checks selected contracts against the published crates.io source.
Version 0.8.2 was the newest non-yanked version in the registry index checked
on 2026-11-27. The archive SHA-256 is
`72c22d99362c7aac7d77efab6b49c2181674b165d7e6e7c755b3432ded64bf51`.
The release archive identifies commit `41a813bd4e7e89a0251bf2fc559c7159933a1066`.
The source lock inventories every archive file and the restored tree stays under
`.work/source`.

See the [independent specification](aeneas/profiles/default/specification.md),
[theorem inventory](aeneas/profiles/default/theorems.json), and
[native findings](verification/findings/README.md).

## Reproduce locally

Use Python 3.11 or newer and the [managed tool prerequisites](../../verification/aeneas-management.md).
On the supported `aarch64-apple-darwin` host, run from this directory:

```sh
bash scripts/setup.sh
cargo +1.94.1 fetch --locked
bash scripts/verify.sh --offline
```

A previously prepared Lake package cache can be selected with
`AENEAS_LAKE_CACHE`. The managed runner checks its dependency revisions and
tracked sources. Verification writes the exact regenerated models, native test
outputs, theorem audit, and compared input fingerprints under `.work/runs/`.
The Cargo lock preserves the release package versions. Its unused Creusot patch
entry accommodates this checkout's ancestor Cargo config. The resolved
dependency graph excludes that package.
