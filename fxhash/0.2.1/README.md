# fxhash 0.2.1 Aeneas verification

This version pins the crates.io `fxhash` 0.2.1 archive in `source.lock.json` (SHA-256 `c31b6d751ae2c7f11320402d34e41349dd1016f8d5d45e48c4312bc8625af50c`). The release bytes are restored to ignored `.work/source`; the library target compiles that source. The independent Cargo workspace omits benchmark-only `fnv` and `seahash` dev dependencies, as disclosed in `source.lock.json`. Benchmark behavior is outside scope.

The selected profile targets `aarch64-apple-darwin`, where `usize` is 64 bits and native byte order is little endian. `toolchain.lock.json` pins unmodified Aeneas `be86ab0f1989d04944292b345b24c435be3ad10a` and Charon `08d7c9d50144bd84848212c24701253585e90d1f` (`patches: []` for both), Rust 1.94.1 for native tests, nightly-2026-09-17 for extraction, and Lean 4.35.0. The locked proofs-rs patches affect CLI preparation and discovery, not Aeneas or Charon.

## Source relationship

The checked Lean model comes from `.work/adapted/lib.rs`, generated deterministically by `scripts/check-adaptation.py` from the locked release. The checker permits only these source changes:

1. Replace `.bitxor(word)` with the equivalent integer `^ word` operation.
2. Rename the private `write` helper and its call to `write_native`, avoiding a generated Lean name collision.
3. On the supported little-endian target, replace three guarded `NativeEndian::read_u32/u64` calls with fixed indexed byte arrays and `from_le_bytes`. An explicit compile-time guard rejects other endianness.

The release's 4/8-byte loop guards ensure every indexed access is in range. The pinned `byteorder` 1.5.0 implementation reads the same prefix with `from_le_bytes` on this target. Source review and finite native differential tests support correspondence; **no Lean theorem proves equivalence between release and adapted Rust**. The release itself remains unchanged and pinned. Original release extraction under `.work/original-probe` exposes an unresolved `BitXor::bitxor` application axiom; the first derived byteorder model also exposed a `Formatter` axiom through `Result::unwrap`. Both were resolved in the derived source without changing Aeneas.

## Proof coverage

The checked generated module contains the real 32-bit and 64-bit byte loops, tails, all three `Hasher` implementations, and their `Default` methods. The maintained inventory maps 24 public API contracts to checked Lean theorems:

| Operations | Proven statement |
| --- | --- |
| `Default` on `FxHasher32`, `FxHasher64`, `FxHasher` | Initial state is zero. |
| `Hasher::finish` on all three | Returns the current state as `u64` without resetting it. |
| `write_u8`, `write_u16`, `write_u32`, `write_u64`, `write_usize` on all three | Total success and exact state update against independent fixed-width mixing specifications. On 32-bit state, 64-bit input is mixed low word first, then high word. |
| `Hasher::write` on all three | Total success and exact state update against the byte algorithm specification for every modeled initial state and byte slice, including empty slices. |

The byte specification mixes consecutive little-endian 4-byte blocks for `FxHasher32`, or 8-byte blocks followed by an optional 4-byte block for `FxHasher64` and native `FxHasher` on the checked target. Each remaining byte is mixed individually; an empty slice leaves the state unchanged. The checked model relates indexed reads and loops to `Spec.write32` and `Spec.write64`. Generic `hash`, `hash32`, `hash64`, collection aliases, inherited `Hasher` methods and standard collection behavior are outside these claims. No cryptographic or collision-resistance claim is made.

## Reproduce locally

From the repository root on the supported host, with the pinned toolchain cache and Rust/Lean installations available:

```bash
CARGO_HOME="$HOME/.cargo" AENEAS_LAKE_CACHE="$PWD/lexical-parse-integer/1.0.6/.work/caller-proofs/.lake/packages" bash fxhash/0.2.1/scripts/setup.sh --offline
CARGO_HOME="$HOME/.cargo" AENEAS_LAKE_CACHE="$PWD/lexical-parse-integer/1.0.6/.work/caller-proofs/.lake/packages" bash fxhash/0.2.1/scripts/verify.sh --offline
```

The cache path above is a local reuse example, not an input required by a fresh setup. The managed runner checks the source and tool locks, regenerates the Lean model byte-for-byte, runs release native tests and finite differential tests separately, rebuilds Lean, audits theorem kinds and transitive axioms, and compares input fingerprints. The repository's inherited `.cargo/config.toml` supplies an unused Creusot patch on this host; it is an execution input reflected in the Cargo locks and logs. The differential script runs Cargo from a temporary directory to avoid that ancestor setting. This local acceptance does not establish portability to another host/configuration or publication through proofs.rs.

See `aeneas/profiles/default/results.md` for the accepted run and exact local evidence identity.
