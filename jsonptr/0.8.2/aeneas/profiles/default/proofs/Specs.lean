import Jsonptr

/-! Independent observations for the release byte validator and index bounds. -/
open Aeneas Aeneas.Std

namespace JsonptrSpec

/-- A tilde whose successor is absent or is neither ASCII 0 nor ASCII 1. -/
def BadEscape (xs : List U8) (j : Nat) : Prop :=
  xs[j]? = some 126#u8 ∧ xs[j + 1]? ≠ some 48#u8 ∧ xs[j + 1]? ≠ some 49#u8

/-- The ASCII delimiter and escape grammar. UTF-8 validity comes from Rust str. -/
def ValidPointer (xs : List U8) : Prop :=
  (xs = [] ∨ xs[0]? = some 47#u8) ∧ ∀ j, ¬ BadEscape xs j

/-- The exact first-error report; offsets count bytes in the original input. -/
def ValidationPost (xs : List U8) (r : core.result.Result Unit jsonptr.pointer.ParseError) : Prop :=
  match r with
  | .Ok () => ValidPointer xs
  | .Err .NoLeadingSlash => xs ≠ [] ∧ xs[0]? ≠ some 47#u8
  | .Err (.InvalidEncoding sep cause) =>
    let d := sep.val
    let j := d + cause.offset.val
    xs[0]? = some 47#u8 ∧ cause.source = .Tilde ∧
      BadEscape xs j ∧ (∀ k, k < j → ¬ BadEscape xs k) ∧
      xs[d]? = some 47#u8 ∧ d < j ∧
      (∀ k, d < k → k < j → xs[k]? ≠ some 47#u8)

/-- Array position denoted by a numeric index or the position after the last item. -/
def indexValue (idx : jsonptr.index.Index) (length : Usize) : Usize :=
  match idx with
  | .Num n => n
  | .Next => length

/-- Existing-element and insertion bounds over the full machine length domain. -/
def BoundsPost {E : Type} (errLength errIndex : E → Usize)
    (inclusive : Bool) (idx : jsonptr.index.Index) (length : Usize)
    (r : core.result.Result Usize E) : Prop :=
  let n := indexValue idx length
  let within := if inclusive then n.val ≤ length.val else n.val < length.val
  match r with
  | .Ok out => within ∧ out = n
  | .Err err => ¬ within ∧ errLength err = length ∧ errIndex err = n

end JsonptrSpec
