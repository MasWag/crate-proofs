# FXHASH-001: Release README collection constructors do not compile

## Identity and classification

- Crate/version: `fxhash/0.2.1`
- Component: release documentation
- Kind: documentation-mismatch
- Confidence: reproduced-at-pinned-inputs
- Resolution: workaround
- First observed / last reproduced: 2026-11-10
- Upstream report: related [issue #1](https://github.com/cbreeden/fxhash/issues/1); no new issue filed
- Upstream fix: current upstream README uses `default()`; release of that documentation change not established. See also [issue #18](https://github.com/cbreeden/fxhash/issues/18).

## Pinned inputs

The registry release is identified by `fxhash/0.2.1/source.lock.json` (SHA-256 `32d87ea1ca2451997277d8e108f24e05f7e742d44aa4333892ad8564c98f8e1e`); the release archive SHA-256 is `c31b6d751ae2c7f11320402d34e41349dd1016f8d5d45e48c4312bc8625af50c`. Its `README.md` SHA-256 is `7b9227f966b312e221bd372fef79438b2446a21241eb7542520eac29bfbc10d0`, and `lib.rs` SHA-256 is `885b72a1c977dc1c3ff4e0652719e62b6d8c3e713403e571afd581283f72df7b`. The examples are in the README's Examples section; `lib.rs` defines the aliases. The run used Rust 1.94.1 on `aarch64-apple-darwin`, Cargo's dev profile and default features, with `byteorder` 1.5.0.

## Expected behavior and its basis

The release README presents examples of building an `FxHashMap` and an `FxHashSet`; copying either example into a Rust program with `fxhash` available should compile.

## Observed behavior

Both examples fail to compile at `::new()` with E0599, reporting no associated function named `new` for the respective `HashMap` or `HashSet` with `BuildHasherDefault<FxHasher>`. The `default()` control compiles and runs successfully. The set example's `insert` calls each take one argument.

## Reproduction

The displayed issue example below is the release README's map example in a `main` function. The checked-in sources are `verification/repro/readme-map.rs` (SHA-256 `d5722ae36ead28981b9120503062c87994f9d7f558abf40d9806a60defc79bd7`), `readme-set.rs` (`b14f7e9b16b46744ec2b3f51393044b1e02c837bd587e9bd6bea9e829524df29`) and `readme-default.rs` (`2aeca7fcd1e503dc2da31bb1c5abcf4ad74fe46bb6c46d7d2b4b8755121f478b`). The independent Cargo manifest and lockfile have SHA-256 `b06c2b8ac9d2411bf28505c8bc4352e9c74802483c9c8f286baaef3e5f9f56cb` and `9385f761d98c5f8cbacaa7619ff6a0efdeb4ce9ed2f4c188133d4a1159a42684` respectively. The manifest uses the restored release source at `.work/source`; restore it before rerunning if absent.

From `/private/tmp`, the recorded commands used `RUSTC=/Users/mwaga/.rustup/toolchains/1.94.1-aarch64-apple-darwin/bin/rustc /Users/mwaga/.rustup/toolchains/1.94.1-aarch64-apple-darwin/bin/cargo check -vv --offline --locked --manifest-path /Users/mwaga/crate-proofs/fxhash/0.2.1/verification/repro/cargo/Cargo.toml --target-dir /Users/mwaga/crate-proofs/fxhash/0.2.1/.work/readme-repro-pinned/target --bin readme-map`, and the same command with `readme-set`; both exited 101. The control used `RUSTC=/Users/mwaga/.rustup/toolchains/1.94.1-aarch64-apple-darwin/bin/rustc /Users/mwaga/.rustup/toolchains/1.94.1-aarch64-apple-darwin/bin/cargo run -vv --offline --locked --manifest-path /Users/mwaga/crate-proofs/fxhash/0.2.1/verification/repro/cargo/Cargo.toml --target-dir /Users/mwaga/crate-proofs/fxhash/0.2.1/.work/readme-repro-pinned/target --bin readme-default` and exited 0. These absolute paths identify the recorded workspace and must be adjusted if it moves. Offline execution also requires the locked dependencies in the Cargo cache.

## Evidence and interpretation

The native run's local-only `.work/readme-repro-pinned/cargo-result.json` has SHA-256 `f3309174841c3808f563d4fd9c9e9b5a63007342091e9870df93245f4fcdac45`. The local-only logs `cargo-readme-map.log`, `cargo-readme-set.log` and `cargo-readme-default.log` in that directory have SHA-256 `1d0cce9a5d126ee11611e7ec5a006bed4c0d9eb6b12c2659e5761bda8048648f`, `1ba2448e925764ab5c5565dc752b26a4ae7f5b8471d336e3880b01e8f65d77a5` and `c2649444b802ff779c3b6af84609b1b1a9d173ebe71be7b3d2412ff5dceb1c3b`. This is native execution evidence, not a formal theorem. The map constructor issue was previously discussed in [issue #1](https://github.com/cbreeden/fxhash/issues/1). Upstream's default branch has changed the README examples to use `default()`, while this record concerns the pinned 0.2.1 release README.

## Cause, impact and proof scope

The examples use a constructor associated with the default standard-library hasher, whereas the aliases select `FxBuildHasher`. This affects users copying the published examples; it does not establish a defect in the hash algorithm. Collection aliases are outside the current verification scope.

## Resolution and regression

Using `FxHashMap::default()` and `FxHashSet::default()` is a workaround, supported by the recorded control. No upstream issue has been created as part of this investigation.

## Issue-ready draft

**Title:** Fix collection constructors in the 0.2.1 release README

### Description

The `fxhash` 0.2.1 README examples call `FxHashMap::new()` and `FxHashSet::new()`, but these aliases use `FxBuildHasher` and the examples do not compile with those constructors.

### Steps to Reproduce

With `fxhash = "=0.2.1"` as a dependency, compile:

```rust
use fxhash::FxHashMap;

fn main() {
    let mut hashmap = FxHashMap::new();
    hashmap.insert("black", 0);
    hashmap.insert("white", 255);
}
```

The README's `FxHashSet::new()` example is affected in the same way.

### Expected Behavior

Both README examples compile and create collections using the Fx hasher.

### Actual Behavior

Compilation fails with E0599: no associated function named `new` is found for the collection with `BuildHasherDefault<FxHasher>`.

### Environment

- `fxhash` 0.2.1; Rust 1.94.1, `aarch64-apple-darwin`

### Screenshots/Logs

The compiler reports E0599 at the `::new()` call.

### Additional Context

`FxHashMap::default()` and `FxHashSet::default()` compile and run in the tested control. The current upstream README already uses `default()`. Related: [#1](https://github.com/cbreeden/fxhash/issues/1) and [#18](https://github.com/cbreeden/fxhash/issues/18).
