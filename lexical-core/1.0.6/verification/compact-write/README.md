# Compact decimal u8 core

> **Native compiler correction:** The original native runs used rustc 1.99.1. Fresh runs explicitly pinned to rustc 1.94.1 reproduce all reported native results; see [the recheck record](../../publication/native-recheck.json). Original evidence remains unchanged.

This independent workspace retains an explicit u8/decimal specialization of lexical-write-integer 1.0.6's compact conversion algorithm. The proof targets `decimal_u8` in this derived input: all 256 representable u8 values and every initial caller buffer of length at least three, with arbitrary contents. It establishes successful termination, canonical ASCII decimal bytes, exact length and preservation of the caller buffer after those bytes. It returns a length and updated buffer; it does not establish a public returned-slice or mutable-borrow backward-function contract.

The maintained proof is in [the compact_write profile](../../aeneas/profiles/compact_write/). Its `Proofs.lean` compares the generated function with an independent arithmetic decimal specification; `decimalAscii_canonical` establishes digit range, no leading zero, length one through three and positional value. The universal theorem composes 256 kernel-checked numeric cases. Initial buffer contents and length are universally quantified in every case. This is finite exhaustion of the complete u8 value domain, with symbolic buffers, rather than native testing.

`generate-cases.py` reconstructs the authored case proofs from a shared prelude and reusable tactic sequences; the generator supplies proof scripts, not trusted answers. Lean checks every arithmetic operation, digit-table lookup, array update, loop termination and slice copy in the generated function. Only ordinary kernel `decide` is used for closed mathematical facts; no native-decision axiom is used. The final managed build/audit result and its source fingerprint belong to the profile's results and run evidence.

## Correspondence to the release

The [derivation checker](derive.py) reads pinned, unchanged registry source, checks hashes and reproduces [src/lib.rs](src/lib.rs). It preserves the release's 128-byte reverse-digit temporary array, quotient/remainder loop and digit table. It performs these explicit specializations:

- Fix `Self` to u8 and radix to decimal 10.
- Remove `Self::BITS <= 128`, which is true for u8.
- Replace the generic conversion of 10 to `Self` with `10u8`, and the generic u8-to-u32 cast with Rust's lossless `as u32`.
- Inline `copy_to_dst` as its original `buffer[..len].copy_from_slice(slc); len` body with concrete byte slices.

The recipe is mechanically checked and source correspondence was reviewed independently. Equivalence to the original generic release function is not a formal theorem. Accordingly the formal mapping names the derived helper, not the unchanged public lexical-core API. No crates.io file, Charon, Aeneas or standard model is modified. No other integer width, radix, sign, format, float algorithm or inadequate-buffer behavior is covered by this core proof.

The unchanged generic compact function was probed first. Charon succeeded, but Aeneas reported `Unreachable` at lexical-util's generic numeric casts (`num.rs:146` and `151`); its partial output was rejected. The original probe is [release-extraction.json](release-extraction.json), with local-only LLBC/logs under `../../.work/compact-write-release2`. The earlier `compact-write-release` attempt stopped at Cargo because the execution directory's unused Creusot patch changed lockfile requirements; it is not algorithm evidence. The original-body diagnostics are retained as recorded probes; this profile does not rerun them during every managed verification. A separate monomorphization experiment reached different array-repeat/AsRef boundaries, documented in the version's probe evidence; it did not verify the release body.

## Native comparison evidence

The [test](tests/correspondence.rs) passed 4,608 comparisons: all 256 values, six buffer lengths and three initial content patterns. It compared the derived function, unchanged release `Compact::compact`, public `lexical_core::write`, Rust's decimal string, exact count, full mutated buffer and suffix preservation. [native-evidence.json](native-evidence.json) records the locked dependencies, archive/source checks, exact command, successful status and full-log digest. The log/build remain local-only ignored `.work/compact-write-native` artifacts. This evidence supports correspondence on those finite native buffer cases; arbitrary-buffer release equivalence remains source-reviewed, not formally proved.

Native tests and extraction run from the version directory and inherit the repository `.cargo/config.toml` patch to an unused Creusot dependency. The lockfile records that unused patch. No Creusot environment is activated; changing `CARGO_HOME` alone would not exclude ancestor configuration. See [execution-config.json](../execution-config.json).

From the repository root, after preparing the locked registry cache:

```sh
python3.11 lexical-core/1.0.6/verification/compact-write/derive.py
python3.11 lexical-core/1.0.6/verification/compact-write/generate-cases.py
env CARGO_HOME=/Users/mwaga/crate-proofs/lexical-core/1.0.6/.work/cargo-home rustup run 1.94.1 cargo test --locked --offline --manifest-path lexical-core/1.0.6/verification/compact-write/Cargo.toml -- --nocapture
```

Use the version's managed `scripts/verify.sh --profile compact_write` for extraction, regeneration comparison, build and theorem audit. See the profile's current results for accepted runs; a standalone Lean build is not managed acceptance.

## 2026-11-10 native compiler provenance correction

The original native run's target `.rustc_info.json` identifies Homebrew rustc 1.99.1, despite the command selecting Cargo through `rustup run 1.94.1`. The earlier Rust 1.94.1 attribution in the retained native evidence describes the intended toolchain, not the compiler actually used. Original logs, manifests and hashes are preserved unchanged.

A fresh recheck explicitly selected the absolute Cargo and rustc 1.94.1 binaries and prepended that toolchain's `bin` directory to `PATH`. Both fresh targets' `.rustc_info.json` confirm `rustc 1.94.1 (e408947bf 2026-03-25)`. Controls passed, the four ignored expected-correct regression assertions and both issue snippets reproduced their documented failures, and all 4,608 compact comparison cases passed. The public issue snippets' Rust 1.94.1 prerequisite is supported by this fresh run. No Rust proof input, generated Lean, specification or formal theorem changed.

See [the append-only native recheck record](../../publication/native-recheck.json) for exact commands, compiler metadata, source/log digests and local-only evidence availability.
