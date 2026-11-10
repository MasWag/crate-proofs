import Specs

/-! Mathematical observables for the decimal block caller.

Specification responsibility: Astra independently reviewed and adopted these
definitions against SCALAR-SPECIFICATION.md after an initial Sol translation.
The input list is the remaining suffix, not the complete original input.
The contract must separately carry the original absolute cursor and the bound
cursor + suffix.length ≤ usize::MAX. No definition below reads generated output.

Only a prefix of exactly four/eight bytes is inspected. The explicit length
condition is essential: zero-padding in byteVal is a totalization for auxiliary
packing arithmetic, not permission to parse a truncated input. Values use
left-to-right positional evaluation, and are promised only for valid blocks.
Packing observables describe the safe adapter; they do not establish the
release's raw unaligned-read, endian, iterator, or generic target-cast bridge.
-/
namespace CallerSpecs

def byteVal (xs : List Aeneas.Std.U8) (i : Nat) : Nat :=
  (xs[i]?.getD 0#u8).val

def pack4 (xs : List Aeneas.Std.U8) : Nat :=
  byteVal xs 0 + 256 * byteVal xs 1 + 65536 * byteVal xs 2 + 16777216 * byteVal xs 3

def pack8 (xs : List Aeneas.Std.U8) : Nat :=
  pack4 xs + 4294967296 * byteVal xs 4 + 1099511627776 * byteVal xs 5 +
    281474976710656 * byteVal xs 6 + 72057594037927936 * byteVal xs 7

def block4Digits (xs : List Aeneas.Std.U8) : Prop :=
  4 ≤ xs.length ∧ ∀ i, i < 4 → LexicalParseIntegerSpec.asciiDigit 10 (byteVal xs i)

def block8Digits (xs : List Aeneas.Std.U8) : Prop :=
  8 ≤ xs.length ∧ ∀ i, i < 8 → LexicalParseIntegerSpec.asciiDigit 10 (byteVal xs i)

def block4Value (xs : List Aeneas.Std.U8) : Nat :=
  LexicalParseIntegerSpec.textValue 10 ((List.range 4).map (fun i => byteVal xs i - 48))

def block8Value (xs : List Aeneas.Std.U8) : Nat :=
  LexicalParseIntegerSpec.textValue 10 ((List.range 8).map (fun i => byteVal xs i - 48))

end CallerSpecs
