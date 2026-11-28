# Verification results

The managed offline verifier passed on 2026-11-28 for profile `default` on
`aarch64-apple-darwin`. The proofs use the unchanged crates.io release. Its
registry archive identifies upstream commit
`8bf933b6c8aa3d1920f69d4dc71f190b626f979d`.
[Source resolution](../../../verification/source-resolution.json) ·
[Source lock](../../../source.lock.json) · [Tool lock](toolchain.lock.json)

## Checked contracts

| API | Checked inputs and observations |
| --- | --- |
| `encode_u32`, `encode_u64`, `encode_s32`, `encode_s64` | All values of the named type. The returned length and bytes describe the shortest encoding. Unused array slots contain zero. |
| `encode_fixed_u32`, `encode_fixed_u64`, `encode_fixed_s32`, `encode_fixed_s64` | All values of the named type. The returned array contains five or ten fixed-length bytes with the specified payloads and continuation bits. |
| `decode_u32`, `decode_u64`, `decode_s32`, `decode_s64` | All arrays of the expected size. Decodes the first complete in-range encoding and returns its consumed length. Returns `None` for invalid input. Padded encodings are accepted. |
| `is_last`, `max_len` | Terminal-byte classification for every byte and ceiling division by seven for every width. |
| `encode_uint_slice` | All five unsigned primitives, widths from zero through storage width, and every cursor at or before the buffer end. Writes the shortest encoding and advances the cursor when it fits. Short capacity writes the fitting prefix and preserves the cursor. Range rejection preserves the entire state. |
| `encode_fixed_uint_slice` | All five unsigned primitives, positive widths through storage width, and every cursor at or before the buffer end. On success, writes exactly the required fixed bytes and advances the cursor. Short capacity or range rejection leaves the state unchanged. |
| `encode_sint_slice` | All five signed primitives, every width, and every cursor at or before the buffer end. Checks the actual release guard and writes the shortest encoding of accepted values. Short capacity writes the fitting prefix and preserves the cursor. Range rejection leaves the state unchanged. |
| `encode_fixed_sint_slice` | All five signed primitives, positive widths through storage width, and every cursor at or before the buffer end. Range rejection and short capacity preserve state. When capacity is enough, a guard-accepted value must fit the fixed groups. Each intended representable value satisfies this premise. Success writes the exact fixed bytes and advances the cursor by the group count. |
| `decode_uint_slice` | All five unsigned primitives and every cursor. Widths from seven through storage width consume at most `floor(BITS / 7) + 1` groups. At multiples of seven, the extra group permits a zero terminator. Below seven, the release bypasses the width limit and accumulates radix contributions truncated to storage width. A present byte at an invalid shift gives modeled overflow. Exhaustion is checked first. |
| `decode_sint_slice` | The four supported signed primitive types and every cursor at widths from zero through storage width. Decodes against the effective signed width, which is one bit larger at multiples of seven. The returned cursor and errors follow the first complete prefix or the relevant failure. |
| `Error` predicates and trait methods | Predicates classify the variants. Clone, equality, cloning into a destination, and inequality follow variant identity. The stable Eq assertion default returns unit. The deprecated standard description returns its fixed text. |
| `Error::source`, `Error::cause` | Rust call observers prove an absent result for either variant. Their optimized MIR inlines the selected standard methods and constructs `None`, and their extracted Boolean result is true. |
| `UInt::BITS`, `SInt::BITS` | Width constants for all ten supported primitives. |

All writer proofs preserve buffer length and bytes outside the written range.
At narrower widths the actual signed writer guard accepts `[-2^BITS, 2^BITS)`.
The fixed signed proof requires that the accepted value fit its groups if there
is enough space to write. The wider guard can admit values which violate that
premise. The native finding documents the resulting release behavior.

For bounded-group decoding, the proofs distinguish exhaustion from an invalid
final group and preserve the cursor on Rust errors. Separate theorems
characterize modeled assertions on oversized widths. See the
[specification](specification.md) for the exact field contracts and the
[theorem inventory](theorems.json) for their coverage and premises.

## Extraction and model boundary

The verifier compared twelve regenerated model files byte for byte, rebuilt
the Lean package and checked all 89 named theorems. The inventory contains
58 callable mappings across 30 API identifiers and 31 supporting declarations.
The audit permits `propext`, `Classical.choice`, and `Quot.sound`.

Aeneas and Charon used their unmodified pinned revisions. The array and error
extractions use default Cargo features. The slice core and concrete writer
harnesses disable default features. The standard error observers use default
features and optimized metadata compiled from the unchanged release. Their
replay retains commands, metadata hashes and inlining evidence from MIR.
The run also records Cargo invocation directories and hashes of inherited
configuration before and after extraction.

The concrete writer model uses Aeneas's split-file external interface for
`max_len`. Its authored support delegates to a separately extracted copy
of the actual release function. The audit checks equality with the existing
helper. A coercion scoped to the concrete writer model maps its generated
`IntErrorKind` into the pinned backend's `TryFromIntError` representation,
`Unit`. The individual generated narrowing functions remain unchanged.
For every masked payload, the proofs establish that those functions take the
successful branch and preserve the payload value. The generated writer bodies
are checked equal to the previously proved algorithm bodies after projecting
the actual trait dictionaries.

## Remaining scope

Display and Debug extraction reaches unsupported dynamic types in the Rust
formatter. The pinned fallback formatter model omits output and writer
failure. Direct translations of the dynamic signatures of `source` and
`cause` retain formatter and trait-model limitations. The checked Rust
observers establish the absence of either result. Arbitrary downstream
macro expansions generate caller-selected functions, while the array proofs
cover the named release expansions. The compiler-only unstable Eq derive
hook is outside the stable callable surface.

## Native observations

The default, release, no-default-features and all-features Cargo profiles
each passed 15 unit and 19 documentation tests. Separate observation
harnesses passed nine debug tests and nine optimized tests. The
[findings](../../../verification/findings/) describe the reproduced cases.

## Local evidence

The accepted run is `.work/runs/default-78nsna0q`. Its pipeline input JSON SHA-256
is `c48c52ee4c08b9d7b2b863d6568ccb779b22897e61b8982e6f5b801ae3452ef4`. Its audit input JSON SHA-256 is
`47afd30a5494148faf4c51160b9fb0a52d670cc07dfabbe5cacaee2ca4e57863`. Each hash matches the corresponding before and after JSON.
The archived descriptor and summary are in [evidence](evidence/).
The earlier [16-theorem acceptance](evidence/accepted-arrays/),
[65-theorem acceptance](evidence/accepted-65/), and
[68-theorem acceptance](evidence/accepted-68/) retain their original evidence.
