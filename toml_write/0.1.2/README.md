# toml_write 0.1.2 verification

The workspace uses the newest non-yanked release shown in the [Cargo registry index capture](verification-release-index.jsonl). The release archive checksum and every file are pinned in [source.lock.json](source.lock.json). Restoration populates an ignored `.work/source` directory, and Cargo compiles that release source.

See the [mathematical specification](SPECIFICATION.md), [default proof profile](aeneas/profiles/default/specification.md), [verification results](aeneas/profiles/default/results.md), and the [quote-run overflow finding](verification/findings/TOML-WRITE-001.md).

The release proofs cover both metric scans, both builders, and ten explicit encoding selectors. The string constructor is proved on both sides of its checked quote-counter boundary. The two default selectors also have proofs for an isolated explicit-match source adaptation. Exact emitted formatting and serialization remain open.

From this directory, use Python 3.11 or newer on `PATH`. The managed profile pins Rust, Aeneas, Charon, Lean, OCaml packages, and Lean package revisions. Follow the repository's [Aeneas management guide](../../verification/aeneas-management.md) for first-time tool setup and cache preparation. The accepted target is `aarch64-apple-darwin`.

```sh
bash scripts/setup.sh
bash scripts/verify.sh --offline
```

If the repository has an ancestor Cargo configuration that adds an unrelated package patch, run `bash scripts/verify-isolated.sh --offline` with the prepared tool, source, and Lake caches. The isolated run copies the current proof files and shared scripts to a temporary directory outside the repository's Cargo configuration. The staging directory is retained with its evidence path.
