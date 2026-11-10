# Radix-parametric packed-word contracts

This profile extends the independent obligations in
[SPECIFICATION.md](../../../SPECIFICATION.md) to each radix `r` with
`2 <= r <= 10`. `proofs/Specs.lean` owns the independent grammar and value
definitions. The byte sequence is read from the least significant packed byte
to the most significant byte, in textual digit order.

For every U32/U64 packed word and every radix in that domain, the corresponding
four/eight-byte recognizer must return Aeneas `.ok out`, with `out = true` iff
every byte is an ASCII digit from `48` through `48+r-1`. Recognition has no
valid-digit input premise. In particular radix 2 rejects ASCII `2`, and all
radices in this profile reject letters and bytes above ASCII `9`.

For every word satisfying that predicate, the corresponding decoder must return
Aeneas `.ok out` with mathematical value equal to `wordValue r count word`.
Leading zero digits are allowed. The positional value uses unbounded Nat
arithmetic, not machine wrapping. Each machine operation, cast, and packed-lane
carry/borrow relation must be discharged by the generated-body proof.

The proposed harness substitutes an explicit radix argument for the release's
`NumberFormat::<FORMAT>::MANTISSA_RADIX` lookup. A theorem for that harness
corresponds only to valid release configurations whose mantissa radix equals
the argument. Availability of a radix in a particular Cargo feature profile is
a separate API/configuration obligation. Source comparison and any source
adaptation are recorded separately from the Lean theorem; neither a textual
comparison nor the theorem alone is a formal Rust-to-Rust equivalence proof.

These contracts do not claim correctness of generic radix byte conversion for
radices above ten, public parser grammar, signs, errors, iterator advancement,
or composition of blocks inside the caller. Those obligations stay explicit in
the main coverage ledger and [scalar contracts](../../../SCALAR-SPECIFICATION.md).
