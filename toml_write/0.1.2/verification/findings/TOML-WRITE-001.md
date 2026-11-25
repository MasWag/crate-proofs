# TOML-WRITE-001: Consecutive quotes overflow string metrics

## Identity and classification

- ID: `TOML-WRITE-001`
- Crate/version: `toml_write/0.1.2`
- Component: release implementation
- Kind: implementation-bug
- Confidence: reproduced-at-pinned-inputs
- Resolution: open
- First observed / last reproduced: 2026-11-25
- Upstream report: not separately reported; related [toml-rs/toml#1188](https://github.com/toml-rs/toml/issues/1188) describes the same cause in a later `toml_writer` release.
- Upstream fix: not checked

## Pinned inputs

The [source lock](../../source.lock.json) has SHA-256 `f01c3b99f700aba92446c703d2ed0b632c570a834454a96918177623a61817f7`; its `src/string.rs` entry matches the registry source used in the native run. The crates.io archive checksum in the reproducer's `Cargo.lock` is `5d99f8c9a7727884afe522e9bd5edbfc91a3312b36a77b5fb8926e4c31a41801`. The registry source `src/string.rs` has SHA-256 `e762cf0b8f0f1e7ef6a4ff8636312d9c5c0e3d072d02235a9fedc22b6c8e548f`. The affected calculation is `ValueMetrics::calculate`, called by `TomlStringBuilder::new` and string `ToTomlValue`. Reproductions used the default `std` feature, Rust 1.94.1, and the `aarch64-apple-darwin` host and target. The default dev profile enables overflow checks; the default release profile disables them. No release source adaptation was used for the native reproducer.

## Expected behavior and its basis

A valid Rust string containing quotes should be accepted by the string builder and encoded as a TOML string; neither API documents a limit on a consecutive quote run. The input consists solely of 256 ASCII double quotes, a valid UTF-8 string, and needs no special precondition. This expectation is for successful handling of the input; it is not a formal theorem about the API.

## Observed behavior

With overflow checks enabled, the constructor panics with `attempt to add with overflow` at the 256th consecutive double quote in `src/string.rs:334`; an apostrophe run panics at line 327. The same panic occurs when calling `ToTomlValue` on these strings. Runs of 256, 257 and 512 panicked for both quote types; lengths 0, 1, 254 and 255 and two 255-quote runs separated by `x` succeeded. The default release-profile run did not panic for these tested cases; this observation alone does not establish output correctness.

## Reproduction

- Reproducer: `verification/findings/repro/src/main.rs`, SHA-256 `74344502dc6f2ba2491673624dbc735d0b90c340ace7c5993403cb6797a96cd4`, with its adjacent manifest and lockfile.
- Working directory: `/private/tmp` (avoids inherited repository Cargo settings).
- Prerequisites: Rust 1.94.1 and the locked crate available in the local Cargo cache.
- Dev command: `cargo +1.94.1 run --offline --locked --manifest-path /Users/mwaga/crate-proofs/toml_write/0.1.2/verification/findings/repro/Cargo.toml --target-dir /Users/mwaga/crate-proofs/toml_write/0.1.2/.work/findings-target -- --expect-overflow`.
- Release command: the same command with `--release` before `--manifest-path`, omitting `-- --expect-overflow`.
- Both commands exited 0 because the harness catches and asserts the expected panics. The dev run emitted the panic diagnostics above; release emitted no panics. Last independently rerun: 2026-11-25 by the primary investigator.

## Evidence and interpretation

Local-only logs: `.work/findings-evidence/debug.log`, SHA-256 `37fb86565d3496f35222c5205755470a519eaf1c9285342cb6b8867baff4d65a`; `.work/findings-evidence/release.log`, SHA-256 `a029744f39b0bf25012af242763243e8ce99a786e60a5ac522d9492e9265a83b`. These are native observations, not formal proof. The short issue example below was also run in a separate temporary locked Cargo harness with Rust 1.94.1 and exited 101 with the same double-quote overflow diagnostic.

## Cause, impact and proof scope

The source increments `u8` counters for consecutive single and double quotes and stores their maxima. With overflow checking, incrementing 255 on the next matching byte panics before construction or serialization completes. This is an implementation behavior, separate from any extraction or model boundary. A total-success claim for these public operations cannot include this input under overflow-checked semantics. No claim about other APIs or profiles follows merely from this observation.

## Resolution and regression

No fix was tested. A regression should cover both quote types at 255 and 256 consecutive characters with overflow checks enabled, as well as separated runs. Upstream communication requires separate authorization.

## Issue draft

Title: String builder panics on 256 consecutive quotes

### Description

In `toml_write` 0.1.2, `TomlStringBuilder::new` panics on a valid string containing 256 consecutive double quotes when overflow checks are enabled. A run of apostrophes also triggers the panic, as does converting the affected string with `ToTomlValue`.

### Steps to Reproduce

With `toml_write = "=0.1.2"`, run this in the default dev profile:

```rust
use toml_write::TomlStringBuilder;

fn main() {
    let input = "\"".repeat(256);
    let _ = TomlStringBuilder::new(&input);
}
```

### Expected Behavior

The builder accepts the valid string so it can be encoded as a TOML string.

### Actual Behavior

The call panics with `attempt to add with overflow` in `ValueMetrics::calculate`.

### Environment

`toml_write` 0.1.2, default features, Rust 1.94.1, default dev profile. The tested default release profile did not panic for this input.

### Additional Context

Related: [toml-rs/toml#1188](https://github.com/toml-rs/toml/issues/1188) reports the same counter overflow in a later `toml_writer` release.
