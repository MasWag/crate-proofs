# Default profile specification

The independent contract and open coverage ledger are in
[SPECIFICATION.md](../../../SPECIFICATION.md). `proofs/Specs.lean` defines the
independent radix fold and original-byte, little-endian packed-word observables.
It contains no implementation-correctness assumption.

The first extraction target is the actual standard decimal parser. If extraction
blocks on that algorithm, a generated four/eight-digit helper theorem may establish
only the named helper obligation. Such a theorem does not establish complete or
partial public parsing. The four/eight-digit recognizers must classify every
machine-word input; decoder theorems may assume their bytes are valid digits.

Before acceptance, record the exact selected generated definitions, enabled
features, target width, source adaptations, dependency models, and theorem
inventory in the profile results. The intended decoder relation is equality of
the machine result's mathematical value to `wordValue radix count word`; the
intended recognizer relation is Boolean truth exactly when
`wordDigits radix count word`. Both require total Aeneas success.

The selected SWAR harness specializes the release bodies to radix 10. Its
release correspondence is restricted to format instantiations whose
`NumberFormat::<FORMAT>::MANTISSA_RADIX` equals 10, including `STANDARD`;
it is not a theorem for all `FORMAT` values or every supported radix.
The source comparison checks the textual specialization and must preserve the
original `u32` type of that constant. This comparison is separate evidence from
the Lean theorem about the generated harness, not a formal Rust equivalence proof.

Any residual pointer/iterator or standard-library model boundary must be stated
explicitly. No iterator assumption may replace the required relation between
actual original-byte positions, returned digits and the consumed prefix. The
maintained theorem audit determines verified scope; this specification does not.
