# block-padding 0.4.2 contracts

Specification responsibility: the independent specification/review agent. Proof
implementation responsibility: the implementation agent. Specification definitions
are in `aeneas/profiles/default/proofs/BlockPadding/Specs.lean`; they import only `Std` and
do not call extracted functions. The source is the pinned crates.io 0.4.2 release.
This document states targets, not proof completion.

## Observations and proof obligations

A block is an arbitrary byte sequence `b`; `B = length b`, and `p` is the message
length. Every original prefix byte and every padding byte is observable. Rust
slice results must be the actual prefix of the input, with the specified length;
mere equality of the length is insufficient. Padding mutates the same buffer,
preserves its length and leaves its prefix unchanged. Machine-size and borrowed
slice invariants belong to the representation bridge, not assumptions about the
algorithm's correctness.

For each valid padding call, prove `∃ out, generated_call = Result.ok out ∧
postcondition out`. For decoding, prove total execution on `UnpadDomain`, with the
inner Rust `Ok` exactly when `Accepted` holds and its slice equal to `b.take p`,
and the inner Rust `Err(Error)` exactly when no such `p` exists. Do not assume an
inner successful return. Outside the nonpanicking domain, preserve the release's
panic behavior in the specification and distinguish a checked panic theorem from
a source observation. An ordinary Rust `Err` is not an Aeneas execution failure.

## Raw algorithms

| Algorithm | Padding nonpanic domain | Exact padding suffix | Decoding |
|---|---|---|---|
| ZeroPadding | `p ≤ B` | `B-p` zeros | remove the maximal trailing sequence of zeros; always succeeds, including empty input |
| NoPadding | `p ≤ B` | no mutation anywhere | return all input bytes, including empty input |
| Pkcs7 | `p < B ≤ 255` | `B-p` repetitions of byte `B-p` | for `1 ≤ B ≤ 255`, final count `n` must satisfy `1 ≤ n ≤ B` and all last `n` bytes must equal `n`; return first `B-n` bytes, otherwise Error |
| Iso10126 | `p < B ≤ 255` | exactly PKCS#7 output | for `1 ≤ B ≤ 255`, accept precisely final count `1 ≤ n ≤ B`; all preceding padding bytes are arbitrary; return first `B-n` bytes, otherwise Error |
| AnsiX923 | `p < B ≤ 255` | `B-p-1` zeros followed by byte `B-p` | for `1 ≤ B ≤ 255`, final count `1 ≤ n ≤ B` and the preceding `n-1` suffix bytes all zero; return first `B-n` bytes, otherwise Error |
| Iso7816 | `p < B` | byte 128 followed by `B-p-1` zeros | accept exactly a suffix consisting of byte 128 followed only by zeros; remove it; empty and all-zero inputs return Error |

All padding calls outside their listed domain panic. PKCS#7, ISO10126 and ANSI
X9.23 decoding panic on empty input and inputs longer than 255; these are release
behaviors, not silent extra premises on the public trait documentation. Empty
decoding is malformed input but the trait promises Error and gives no nonempty
precondition. This malformed-input-to-Error requirement fails: native tests on
the release reproduce the three empty-input panics in debug and release builds.
Any proof restricted to `UnpadDomain` therefore leaves this documented requirement
unsatisfied and is not an all-input raw-decoder correctness claim.
Oversized blocks expose an algorithm bound omitted from the generic
method's documentation. ZeroPadding and NoPadding accept `p = B`, including
`p = B = 0`; other schemes cannot pad an empty buffer.

NoPadding intentionally returns uninitialized-message tail *contents already in
the supplied buffer*: these are ordinary initialized bytes, not Rust uninitialized
memory. Its raw API deliberately accepts partial message lengths. Exact recovery
of a message by NoPadding requires `p = B`. ZeroPadding intentionally loses any
trailing zeros of the message: its roundtrip recovers the message after stripping
those zeros. The other four schemes recover exactly the original message prefix
on every padding-domain input. ISO10126 uses deterministic PKCS#7 padding in this
release; no randomness, entropy, or unpredictability claim is made or required by
this crate's documented variation.

## Generic methods, defaults, and data constructors

`Padding::pad` and `Padding::unpad` must refine the respective raw algorithm on
the full fixed-size array, retaining all block-size restrictions above. Their
genericity does not establish facts about arbitrary downstream implementations
of the public trait.

For `pad_detached`, require positive block size `B` and, for the three count-byte
schemes, `B ≤ 255`. Split the data into unchanged full blocks and a unique tail of
length `r < B`. ZeroPadding and NoPadding return `NoPad` precisely when `r = 0`.
For `r > 0`, NoPadding returns `Error`, ZeroPadding returns `Pad` with a zero-filled
tail. The other four algorithms always return `Pad`, including empty data and
aligned data, with an additional correctly padded block. The returned full-block
slice aliases the corresponding input prefix. `DetachedResult` records all data
and the exact variant. Zero-size generic arrays remain explicit boundary work:
chunking behavior must be established from the dependency before any all-size
claim. Do not assume every `ArraySize` is positive without checking its trait.

`unpad_blocks` for ZeroPadding removes all trailing zeros from the flattened
input, potentially spanning several blocks, and succeeds on an empty block list.
NoPadding returns the entire flattened input and also succeeds on an empty list.
For the other four schemes, an empty block list returns Error; for nonempty lists,
only the last block is decoded and the unchanged preceding blocks are retained.
Malformed last-block padding returns Error. Their last block must obey the raw
decoder's nonpanic domain. Valid Rust slice layouts must justify flattening and
the prefix-length multiplication/addition. Do not claim padding validation over
earlier blocks. `BlocksAccepted` specifies the exact retained length.

`PaddedData::unwrap` returns precisely the stored block slice and tail array for
`Pad`, with no byte changes. It panics for `NoPad` and `Error`. Error formatting
writes exactly `Padding error`; standard derive/marker behavior and the public
`array` re-export are separate from padding correctness.

## Complete coverage ledger

Initial status is **unproved** for every entry below. Extraction, native tests,
model helper lemmas, and compilation do not upgrade this status. The final theorem
inventory and results must identify which exact entries are proved, blocked, or
excluded, with theorem names and premises. Preserve this entire ledger even when
only a subset can be verified.

| Entry family | Concrete instances / obligations |
|---|---|
| `raw_pad` | ZeroPadding, Pkcs7, Iso10126, AnsiX923, Iso7816, NoPadding: all-byte mutation, success domain, invalid-position and size panic boundaries |
| `raw_unpad` | all six: exact accepted prefix, total success/error partition, empty-input and size boundaries |
| private `Pkcs7::unpad` | strict=true and strict=false checked bridge, including malformed suffixes |
| `Padding::pad` | each of the six inherited generic instantiations; delegation plus representation bridge |
| `Padding::unpad` | each of the six inherited generic instantiations; delegation plus representation bridge |
| `pad_detached` | default for Pkcs7, Iso10126, AnsiX923, Iso7816; overrides for ZeroPadding and NoPadding; all variants, aligned/empty data, full-block and tail contents |
| `unpad_blocks` | default for Pkcs7, Iso10126, AnsiX923, Iso7816; overrides for ZeroPadding and NoPadding; empty list, malformed last block, all returned bytes |
| `PaddedData::unwrap` | Pad success and both non-Pad panic arms |
| `Error` | Display, core::error::Error marker, derived Clone/Copy/Debug |
| public algorithm marker types | derived Clone/Copy/Debug for all six |
| `PaddedData` | public variant/field representation and derived Debug |
| `array` re-export | dependency surface; no inherited claim that hybrid-array is verified |
| roundtrip laws | four reversible schemes; ZeroPadding maximal-zero removal; NoPadding full-block preservation |

Source adaptations, if necessary, may replace unsupported Rust idioms while
retaining these contracts. Record exact release-to-adapted correspondence and
remaining trust. Aeneas itself remains unchanged. No result for a hand-written
surrogate algorithm alone discharges the release's API obligations.
