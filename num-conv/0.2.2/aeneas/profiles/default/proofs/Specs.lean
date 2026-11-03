import Std

/-!
Independent mathematical observables for num-conv 0.2.2.

These definitions do not call the implementation or Aeneas casts. Widths of the
concrete Rust types are positive. `Int` remainder by the positive powers of two
below is Euclidean remainder, including for negative inputs.

Public implementation theorems must additionally establish unconditional execution
success; these predicates describe returned values and do not assume success.
-/

namespace NumConvSpec

def modulus (bits : Nat) : Int := (2 : Int) ^ bits

def unsignedMin : Int := 0

def unsignedMax (bits : Nat) : Int := modulus bits - 1

def signedMin (bits : Nat) : Int := -modulus (bits - 1)

def signedMax (bits : Nat) : Int := modulus (bits - 1) - 1

def inRange (lo hi value : Int) : Prop := lo ≤ value ∧ value ≤ hi

def preservesValue (input output : Int) : Prop := output = input

def wrapUnsigned (bits : Nat) (value : Int) : Int :=
  value % modulus bits

def wrapSigned (bits : Nat) (value : Int) : Int :=
  (value + modulus (bits - 1)) % modulus bits - modulus (bits - 1)

def saturate (lo hi value : Int) : Int :=
  max lo (min hi value)

def checked (lo hi value : Int) : Option Int :=
  if lo ≤ value ∧ value ≤ hi then some value else none

/-- An equivalent specification form: range plus congruence uniquely selects the
    correct mathematical integer. Use only with the destination's true bounds. -/
def boundedCongruent (bits : Nat) (lo hi input output : Int) : Prop :=
  inRange lo hi output ∧ output % modulus bits = input % modulus bits

end NumConvSpec
