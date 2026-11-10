import Init

/-! Independent low-radix byte grammar and positional values. The radix domain
is an explicit theorem premise; no generated function defines these models. -/
namespace LexicalParseIntegerRadixSpec

def byteAt (word index : Nat) : Nat := (word / 256^index) % 256

def asciiDigit (radix byte : Nat) : Prop := 48 ≤ byte ∧ byte < 48 + radix

def wordDigits (radix count word : Nat) : Prop :=
  ∀ i, i < count → asciiDigit radix (byteAt word i)

def textValue (radix : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun value digit => radix * value + digit) 0

def wordValue (radix count word : Nat) : Nat :=
  textValue radix ((List.range count).map (fun i => byteAt word i - 48))

def radixDomain (radix : Nat) : Prop := 2 ≤ radix ∧ radix ≤ 10

def digits4 (radix word : Nat) : Prop := wordDigits radix 4 word
def digits8 (radix word : Nat) : Prop := wordDigits radix 8 word
def value4 (radix word : Nat) : Nat := wordValue radix 4 word
def value8 (radix word : Nat) : Nat := wordValue radix 8 word

end LexicalParseIntegerRadixSpec
