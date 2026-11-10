import LexicalParseInteger

/-!
Independent mathematical observables. These definitions do not call generated
parser functions and do not assert their correctness. Digits are listed in text
order, which is least-significant-byte first in a little-endian packed word.
-/
namespace LexicalParseIntegerSpec

def byteAt (word index : Nat) : Nat :=
  (word / 256 ^ index) % 256

def asciiDigit (radix byte : Nat) : Prop :=
  48 ≤ byte ∧ byte < 48 + radix

def wordDigits (radix count word : Nat) : Prop :=
  ∀ i, i < count → asciiDigit radix (byteAt word i)

def textValue (radix : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun value digit => radix * value + digit) 0

def wordValue (radix count word : Nat) : Nat :=
  textValue radix ((List.range count).map (fun i => byteAt word i - 48))

def packLittleEndian : List Nat → Nat
  | [] => 0
  | byte :: rest => byte + 256 * packLittleEndian rest

def decimal4Digits (word : Nat) : Prop := wordDigits 10 4 word
def decimal8Digits (word : Nat) : Prop := wordDigits 10 8 word
def decimal4Value (word : Nat) : Nat := wordValue 10 4 word
def decimal8Value (word : Nat) : Nat := wordValue 10 8 word

def unsignedBound (width : Nat) : Nat := 2 ^ width - 1
def signedPositiveBound (width : Nat) : Nat := 2 ^ (width - 1) - 1
def signedNegativeMagnitudeBound (width : Nat) : Nat := 2 ^ (width - 1)

/-- Mathematical lane identity for four decimal digits. This theorem is about
natural-number arithmetic only, not an extracted machine operation. -/
theorem decimal4PackedArithmetic (a b c d : Nat)
    (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) :
    let n := a + 256*b + 65536*c + 16777216*d
    let p := n*10 + n/256
    (p%128)*100 + (p/65536)%128 = 1000*a + 100*b + 10*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*10 +
      (b + 256*c + 65536*d))%128 = 10*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*10 +
      (b + 256*c + 65536*d))/65536 = 10*c + d + 2560*d := by omega
  rw [hhi]
  have hh : (10*c + d + 2560*d)%128 = 10*c + d := by omega
  rw [hh]
  omega

end LexicalParseIntegerSpec
