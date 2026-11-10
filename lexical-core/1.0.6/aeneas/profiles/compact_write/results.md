# Compact writer results

> **Native compiler correction:** The original native runs used rustc 1.99.1. Fresh runs explicitly pinned to rustc 1.94.1 reproduce all reported native results; see [the recheck record](../../../publication/native-recheck.json). Original evidence remains unchanged.

The frozen managed run `compact_write-ufg0jwe_` passed on aarch64-apple-darwin: exact regeneration comparison, a clean local Lean build, all three named theorem audits, checked source archives and restoration, derivation and case-generation checks, and identical before/after input fingerprints. [The acceptance summary](evidence/summary.json) records the exact run and log digests. The fresh Cases build took 245 seconds; the universal proof module then built in 11 seconds. The selected derived helper specializes lexical-write-integer 1.0.6's compact writer to decimal `u8`. The maintained inventory names the total-success theorem, its weakest-precondition support theorem, and an independent canonical-decimal model theorem; only the total-success theorem is mapped to the derived helper. The contract covers all 256 `u8` values and arbitrary initial buffers of length at least three: exact decimal ASCII prefix and count, and unchanged suffix. The proof splits on each value while retaining symbolic buffers.

The transformation and evidence are described in the [compact writer README](../../../verification/compact-write/README.md). The recipe checks pinned release inputs, specializes the type and radix, makes casts concrete and inlines the byte-slice copy. It is not a formal equivalence theorem. The unchanged generic release extraction is blocked by Aeneas at numeric casts. This helper returns a count and updated buffer; it does not prove the public returned-slice or backward-function contract. Other integer types, radices and formatting options, inadequate buffers, parsers and float writers remain open.

Separately, native tests passed 4,608 comparisons over all u8 values, six buffer lengths and three initial patterns against the unchanged compact implementation, public writer and Rust decimal string. These finite observations support correspondence but do not prove it for arbitrary buffers. The same accepted managed run reran this native comparison test successfully; its native status is separate from the formal contracts.

## Reproduce the accepted local run

From the repository root, with the pinned offline caches already prepared, the exact command was:

```sh
AENEAS_LAKE_CACHE=$PWD/lexical-parse-integer/1.0.6/.work/build/sign/aarch64-apple-darwin/proofs/.lake/packages bash lexical-core/1.0.6/scripts/verify.sh --profile compact_write --offline
```

The wrapper sets `CARGO_HOME` to the version-local `.work/cargo-home`. Managed setup selected `.work/tools/b2f666ef0902d4b779bbbb0f81e7b9b90d1fe3f630dda0dfe475b7e35c1acd4e` and checked its locked source trees and binary identities. The dependency donor above is local to this checkout; setup validates its pinned revisions and clean sources before reuse. The configured native Rust pin was 1.94.1, but the accepted managed run inherited Homebrew `cargo`/`rustc` 1.99.1 earlier on `PATH`; `RUSTUP_TOOLCHAIN` alone did not select the rustup proxies. The native target cache `.work/build/native/aarch64-apple-darwin/.rustc_info.json` records rustc 1.99.1 and `/opt/homebrew/Cellar/rust/1.99.1`. The runtime fingerprint recorded the installed rustup 1.94.1 binaries rather than enforcing the binaries used by those native commands. Native test success is preserved with this execution-version correction. Extraction used nightly-2026-09-17 and formal proofs used Lean 4.35.0; their claims are unchanged. Aeneas and Charon had no source patches. The inherited Cargo configuration is checked by `verification/execution-config.json`; no Creusot environment was activated.

- Result: `.work/runs/compact_write-ufg0jwe_/result.json`, SHA-256 `d9f903986a2c69edb1e88e3e900a001671cf82b2366fc9ab30d10e1368d9eeb1`.
- Identical before/after fingerprints: `50a4f676eb9c7dd53a6d83164d1f86fd59d4e05c2223159eaba10060e1101606`.
- Transitive axiom audits allow only `propext`, `Classical.choice`, and `Quot.sound`; all configured named theorems passed.

Raw LLBC, generated files, build logs and audit logs remain local-only under the run directories. These local results establish the stated adapted/conditional scopes, not whole-crate verification, formal release equivalence, CLI proof recording or publication.

The initial independent 4,608-comparison run also used Homebrew rustc 1.99.1, as recorded in its native target cache. Its Rust 1.94.1 metadata came from a direct toolchain query; invoking `rustup run 1.94.1 cargo` did not guarantee Cargo selected that compiler. A separate explicit-compiler Rust 1.94.1 recheck is being recorded under `publication/native-recheck`; it does not rewrite the original observations or formal run hashes. All native observations remain separate from the formal proof.

## 2026-11-10 native compiler provenance correction

The original native run's target `.rustc_info.json` identifies Homebrew rustc 1.99.1, despite the command selecting Cargo through `rustup run 1.94.1`. The earlier Rust 1.94.1 attribution in the retained native evidence describes the intended toolchain, not the compiler actually used. Original logs, manifests and hashes are preserved unchanged.

A fresh recheck explicitly selected the absolute Cargo and rustc 1.94.1 binaries and prepended that toolchain's `bin` directory to `PATH`. Both fresh targets' `.rustc_info.json` confirm `rustc 1.94.1 (e408947bf 2026-03-25)`. Controls passed, the four ignored expected-correct regression assertions and both issue snippets reproduced their documented failures, and all 4,608 compact comparison cases passed. The public issue snippets' Rust 1.94.1 prerequisite is supported by this fresh run. No Rust proof input, generated Lean, specification or formal theorem changed.

See [the append-only native recheck record](../../../publication/native-recheck.json) for exact commands, compiler metadata, source/log digests and local-only evidence availability.
