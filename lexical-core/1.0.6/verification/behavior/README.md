# Unchanged-release native reproductions

> **Native compiler correction:** The original native runs used rustc 1.99.1. Fresh runs explicitly pinned to rustc 1.94.1 reproduce all reported native results; see [the recheck record](../../publication/native-recheck.json). Original evidence remains unchanged.

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

## 2026-11-10 native compiler provenance correction

The original native run's target `.rustc_info.json` identifies Homebrew rustc 1.99.1, despite the command selecting Cargo through `rustup run 1.94.1`. The earlier Rust 1.94.1 attribution in the retained native evidence describes the intended toolchain, not the compiler actually used. Original logs, manifests and hashes are preserved unchanged.

A fresh recheck explicitly selected the absolute Cargo and rustc 1.94.1 binaries and prepended that toolchain's `bin` directory to `PATH`. Both fresh targets' `.rustc_info.json` confirm `rustc 1.94.1 (e408947bf 2026-03-25)`. Controls passed, the four ignored expected-correct regression assertions and both issue snippets reproduced their documented failures, and all 4,608 compact comparison cases passed. The public issue snippets' Rust 1.94.1 prerequisite is supported by this fresh run. No Rust proof input, generated Lean, specification or formal theorem changed.

See [the append-only native recheck record](../../publication/native-recheck.json) for exact commands, compiler metadata, source/log digests and local-only evidence availability.
