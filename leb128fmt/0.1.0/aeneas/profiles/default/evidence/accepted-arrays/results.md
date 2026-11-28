# Verification results

The managed offline verifier passed on 2026-11-28 for profile `default` on
`aarch64-apple-darwin`. Formal extraction used default Cargo features and
the unchanged crates.io release. The official sparse registry index listed
0.1.0 as its only version, with the archive checksum in the source lock.
The release archive identifies upstream commit
`8bf933b6c8aa3d1920f69d4dc71f190b626f979d`.
[Source resolution](../../../../../verification/source-resolution.json) ·
[Source lock](../../../../../source.lock.json) · [Tool lock](../../toolchain.lock.json)

## Checked contracts

| APIs | All-input guarantee in the extracted model |
| --- | --- |
| `encode_u32`, `encode_u64`, `encode_s32`, `encode_s64` | Successful shortest encoding, exact length and payload bytes, with zero in every unused array slot |
| `encode_fixed_u32`, `encode_fixed_u64`, `encode_fixed_s32`, `encode_fixed_s64` | Successful five- or ten-byte encoding with the specified zero or sign extension and continuation bits |
| `decode_u32`, `decode_u64`, `decode_s32`, `decode_s64` | Successful computation on every array, returning the first terminated, in-range value and consumed length or returning `None` for invalid inputs |
| `is_last`, `max_len` | Terminal-byte classification and ceiling division by seven for every scalar input |
| `Error::is_more_bytes_needed`, `Error::is_invalid_encoding` | True exactly for the indicated error variant |

The decoder contracts admit padded encodings and ignore the bytes after the
first terminator. The [specification](../../specification.md), [theorem
inventory](../../theorems.json) and [report mappings](../../proofs.toml) list the conditions
and exact scope.

The runner matched all five regenerated Lean model files byte-for-byte,
cleaned the local Lake package, rebuilt the proofs and checked transitive axiom
dependencies of the 16 named theorems. The audit permits only `propext`,
`Classical.choice` and `Quot.sound`. The proofs rely on the pinned extraction
and Aeneas scalar, bit-vector, indexing and array models. Aeneas and Charon were
unmodified, and no Rust source adaptation was applied. The proofs-rs CLI
has the preparation and API-discovery patches listed in the tool lock.

The six generic slice codecs were extracted and their generated Lean
typechecked in separate probes. Their functional proofs remain open, including
trait-operation semantics and the resulting cursor and buffer state. Native
counterexamples falsify intended width contracts for several parameterized
operations. Arbitrary macro expansions, formatting and marker traits fall
outside the audited scope.

## Native observations

Each of the default, release, no-default-features and all-features Cargo test
runs passed 15 unit tests and 19 doctests. Separate debug and optimized
observation harnesses reproduced four release issues, with five passing
observation and control tests in each configuration. See the [finding
records](../../../../../verification/findings/) for the cases. The harnesses assert
the observed behavior and serve as native reproductions.

## Local evidence

The latest accepted run is `.work/runs/default-o4uf696h`. The pipeline input JSON
SHA-256, identical before and after, is `17071e654cf1aac38d1ad2ef8c2dbbc114c8e3cfe651323f66356382e0dd027f`. The audit input JSON
SHA-256, identical before and after, is `dca045d2411434ec0a7b3ab19fd15142eb3b7a3259fcc7a0a595baec8a2c4d9f`.

The [summary](evidence/summary.json) records the accepted results and artifact
hashes. The [archive descriptor](evidence/archive.json) identifies the full
local-only archive under `.work/evidence-archives/`. This was a local
verification and report-mapping audit. Proofs.rs recording and publication
were not performed, and the issue drafts were not submitted.
