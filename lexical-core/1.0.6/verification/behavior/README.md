# Unchanged-release native reproductions

This independent Cargo workspace calls the registry `lexical-core =1.0.6` APIs with `parse-integers,format,power-of-two` and default features disabled. The committed lockfile resolves lexical-parse-integer 1.0.6 and lexical-util 1.0.7. It uses no path override or modified release source.

On 2026-11-10, Rust 1.94.1 on aarch64-apple-darwin passed the control test and failed all four ignored assertions of expected correct behavior. Each issue snippet also compiled and failed its assertion as a separate Cargo example. Exact argv, source/archive identities and complete-log digests are in [evidence.json](evidence.json); full logs/build output remain local-only in `../../.work/behavior`.

After preparing the locked cache, from the repository root:

```sh
bash lexical-core/1.0.6/verification/behavior/run.sh
```

The runner changes cwd to `/private/tmp` so Cargo does not inherit this repository's `.cargo/config.toml`, which patches the unrelated Creusot dependency. `CARGO_HOME` alone would not isolate ancestor configuration. The runner succeeds only when controls pass and the ignored regression suite exits 101; inspect the log for the four expected failures. This runner checks the suite's exit status, not the detailed diagnostic text.

For an individual issue snippet, from `/private/tmp`:

```sh
env CARGO_HOME=/Users/mwaga/crate-proofs/lexical-core/1.0.6/.work/cargo-home CARGO_TARGET_DIR=/Users/mwaga/crate-proofs/lexical-core/1.0.6/.work/behavior/target rustup run 1.94.1 cargo run --locked --offline --manifest-path /Users/mwaga/crate-proofs/lexical-core/1.0.6/verification/behavior/Cargo.toml --example lc_001
```

Use `lc_002` for the suffix example. Both examples are expected to exit 101 at the assertion on the unchanged release. No source fix is installed or claimed. See [findings](../findings/README.md) for interpretation.
