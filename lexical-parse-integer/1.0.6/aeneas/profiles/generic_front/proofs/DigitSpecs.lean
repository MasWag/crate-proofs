import Init

/-! Independent ASCII digit semantics, authored by Astra from SPECIFICATION.md.
The model uses three disjoint ASCII ranges, not the implementation's character
normalization or machine arithmetic. The theorem domain is radix 2 through 36;
all byte values, including punctuation and non-ASCII bytes, remain in scope.
-/
namespace LexicalParseIntegerDigitSpec

/-- ASCII digit value before restricting it to the selected radix. Uppercase
and lowercase letters have the same values, from ten through thirty-five. -/
def asciiValue (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte ≤ 57 then some (byte - 48)
  else if 65 ≤ byte ∧ byte ≤ 90 then some (byte - 65 + 10)
  else if 97 ≤ byte ∧ byte ≤ 122 then some (byte - 97 + 10)
  else none

/-- A byte denotes a digit precisely when it has an ASCII alphanumeric value
strictly below the radix. Other characters and out-of-radix digits return none.
This definition is total; supported-radix bounds belong to the Rust theorem. -/
def digit (radix byte : Nat) : Option Nat :=
  match asciiValue byte with
  | some value => if value < radix then some value else none
  | none => none

end LexicalParseIntegerDigitSpec
