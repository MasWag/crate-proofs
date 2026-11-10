# fxhash 0.2.1 mathematical specification

Specification owner: Astra. Implementation/proof owner: Sol. The primary agent
reviews source identity, contracts, proof evidence, and coverage. This document
states intended contracts, not a claim that their implementation proofs are closed.
The release archive and source inventory are authoritative. On 2026-11-10, this
specification was checked against the captured 0.2.1 release `lib.rs` at
`.work/release-review/source/lib.rs` (SHA-256
`885b72a1c977dc1c3ff4e0652719e62b6d8c3e713403e571afd581283f72df7b`).
The release differs from upstream master:
its 32-bit multiplier is the low half of the 64-bit multiplier, and it mixes
remaining bytes individually rather than using two-byte tail words.

## State and observables

For width `w` in `{32,64}`, a state is any integer `h` with `0 <= h < 2^w`.
No reachability-from-default restriction is permitted. Although fields are private,
the internal proof covers the complete scalar representation. `FxHasher32` has
width 32, `FxHasher64` width 64, and `FxHasher` the selected pointer width.
Default state is zero. `finish` returns `h` as a 64-bit unsigned value and leaves
the state unchanged: no reset or extra mixing round. Clone, if selected, copies
the exact state; Debug formatting is outside this model.

Let `K32 = 0x27220a95` and `K64 = 0x517cc1b727220a95`.
The independent word transition is

```
rot_w(h) = (32*h mod 2^w) + floor(h / 2^(w-5))
mix_w(h,x) = ((rot_w(h) XOR x) * Kw) mod 2^w.
```

Arguments `h,x` are width-w words. The rotation summands occupy disjoint bit
positions. Multiplication is mathematical multiplication followed by reduction;
overflow is intended modular behavior, not a precondition failure. This definition
must not call an extracted function or assume an extracted result.

## Byte algorithm

Bytes have values in `[0,256)`. Decode k bytes as `sum_i b[i]*256^i` on a
little-endian target or `sum_i b[i]*256^(k-1-i)` on a big-endian target. Chunk
values are zero-extended to width w. Endianness matters even for fixed-width hashers.

`words32(bs)` takes every complete four-byte block in order, then mixes each of
the remaining zero to three bytes individually. `words64(bs)` takes every complete
eight-byte block, then a four-byte block if available, then mixes each of the
remaining zero to three bytes individually. Every byte occurs exactly once, in order;
no padding or length word is inserted. Define

```
write_w(h,bs) = foldl mix_w h (words_w(bs)).
```

Empty input preserves the state. Public `Hasher::write` must succeed and replace
the state with this value for every representable slice and valid initial state.
Private `write32`, `write64`, and native `write` have the same total-result contract.
Full block loops and all tails are required core coverage; accessor or constructor
proofs cannot replace them. Bounds for byteorder reads and slice operations must
follow from guards, not additional caller assumptions.

## Integer writes and native width

For width 64, `write_u8`, `write_u16`, `write_u32`, `write_u64`, and `write_usize`
perform one `mix64` with the mathematical unsigned input. For width 32,
`write_u8`, `write_u16`, and `write_u32` perform one `mix32`; `write_u64(x)` is
`mix32(mix32(h,x mod 2^32), floor(x/2^32))`. A 32-bit `usize` uses one round;
a 64-bit `usize` input to `FxHasher32` uses the same two rounds as `write_u64`.
Native `FxHasher` selects these rules by pointer width. Integer low/high ordering
is independent of byte endianness. Signed and 128-bit methods inherited from std
require separate inspection and proofs against the pinned standard library.

The Lean `mixNative` definition uses `System.Platform.numBits`, matching Aeneas's
`Usize` representation. Its reduced 64-bit seed equals `K32` at width 32 and `K64`
at width 64. This definition has been independently reviewed by the specification
owner. Rust-to-model correspondence also requires the Lean word width to match the
extracted Rust target. This profile selects a 64-bit Rust target; in particular its
native `write_u64` body is one round. Do not interpret a theorem about that selected
body as verification of the two-round native `write_u64` on a 32-bit Rust target.

## Composition and generic Hash

A trace records method identity, arguments, and call order. Its semantics is the
ordered composition of these transitions; `finish` does not change its state.
Two byte writes mean `write_w(write_w(h,a),b)`, not `write_w(h,a ++ b)`.
A wide integer write need not equal multiple byte writes. The Rust
[Hasher contract](https://doc.rust-lang.org/std/hash/trait.Hasher.html) explicitly
allows these differences. Equal traces from equal states yield equal outputs.
Collisions, including zero-input collisions, do not alone violate that contract.

`hash32`, `hash64`, and `hash` initialize zero, invoke caller-supplied `Hash::hash`,
then observe the state with the appropriate narrowing. Arbitrary `T: Hash` can
panic or diverge, so unconditional total success is impossible. Generic theorems
must assume total success of the supplied operation and an explicit state/trace
postcondition, and return its trace result. This is conditional composition, not
verification of arbitrary Hash implementations or equality/prefix-free obligations.

## Contract shape and exclusions

Implementation theorems require total success, e.g.
`exists out, generated_write state bytes = Result.ok out AND
 stateValue(out) = write_w(stateValue(state), byteValues(bytes))`.
Mutable-state tuples must follow actual generated signatures. Default and finish
also require success. Equality without success, partial WP, or implications from
successful execution do not suffice. Ordinary scalar/slice bounds come from Rust
representations; do not impose artificial state or length restrictions.

Both fixed widths remain ledger obligations. Native width and endianness coverage
is limited to extracted/audited targets; defining both mathematical cases does not
verify unextracted targets. Exclusions: `FxHashMap`, `FxHashSet`, `FxBuildHasher`,
std container algorithms, cryptographic security, collision resistance, distribution
quality, resource usage, and arbitrary downstream Hash implementations.
Byteorder/std operations need checked implementation bridges or clearly disclosed
existing model boundaries; no fresh custom axioms. Any Rust adaptation needs a
separate release-correspondence argument, independent of closed functional goals.

Priority: word mixing; full byte loops/tails; public byte writes; integer writes;
finish/default/clone; conditional generic composition. Record blocked core goals
separately from proven APIs and native regression tests.
