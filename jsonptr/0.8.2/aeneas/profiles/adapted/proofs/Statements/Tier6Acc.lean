import Statements.Common

/-!
# Tier 6 contracts (specification section 21), adapted bodies

Accessors and byte-identity views of byte pointers, equality and order. Every
`PartialEq`/`PartialOrd` impl among `Pointer`, `&Pointer`, `PointerBuf`,
`str`, `&str` and `String` reduces in the release to `str` equality or
`str::cmp`; one adapted function stands for all of them (correspondence note
in the ledger). `Pointer::as_str`, and the derived impls on `Index`,
`InvalidEncoding` and the plain error structs, extract unchanged and are in
`Statements.DefaultDerived`.
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrExtSpec

/-- `Pointer::is_root`, `is_empty`. -/
def IsRootContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ b, jsonptr.adapted_api.is_root_adapted xs = .ok b ∧
    (b = true ↔ bytes xs = [])

/-- `Pointer::len`. -/
def LenContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ n, jsonptr.adapted_api.len_adapted xs = .ok n ∧
    n.val = (bytes xs).length

/-- Equality among the string-backed types, and `Token` equality on encoded
bytes. Stated for all byte slices (no invariant is needed). -/
def StrEqContract : Prop :=
  ∀ a b : Slice U8, ∃ r, jsonptr.adapted_api.str_eq_adapted a b = .ok r ∧
    (r = true ↔ bytes a = bytes b)

/-- Order among the string-backed types, and `Token` order: lexicographic on
bytes (`bytesLt`). -/
def StrCmpContract : Prop :=
  ∀ a b : Slice U8, ∃ o, jsonptr.adapted_api.str_cmp_adapted a b = .ok o ∧
    OrderingAgrees o (bytes a) (bytes b)

/-- `partial_cmp` for the string-backed types is `Some` of the `cmp` result. -/
def StrPartialCmpContract : Prop :=
  ∀ a b : Slice U8, ∃ o, jsonptr.adapted_api.str_cmp_adapted a b = .ok o ∧
    jsonptr.adapted_api.str_partial_cmp_adapted a b = .ok (some o) ∧ OrderingAgrees o (bytes a) (bytes b)

/-- Derived `PartialEq` of `Component`: structural, tokens by encoded bytes. -/
def ComponentEqContract : Prop :=
  ∀ a b : jsonptr.adapted_api.ComponentAdapted,
    ∃ r, jsonptr.adapted_api.component_eq_adapted a b = .ok r ∧
      (r = true ↔ component a = component b)

/-- The order on `Component`: `Root` first, then tokens by `bytesLt`. -/
def componentLt : Component → Component → Bool
  | .root, .root => false
  | .root, .token _ => true
  | .token _, .root => false
  | .token x, .token y => bytesLt x y

/-- Derived `Ord` of `Component`. -/
def ComponentCmpContract : Prop :=
  ∀ a b : jsonptr.adapted_api.ComponentAdapted,
    ∃ o, jsonptr.adapted_api.component_cmp_adapted a b = .ok o ∧
      match o with
      | .lt => componentLt (component a) (component b) = true
      | .eq => component a = component b
      | .gt => componentLt (component b) (component a) = true

/-- Derived `Clone` of `PointerBuf`. -/
def BufCloneContract : Prop :=
  ∀ buf : alloc.vec.Vec U8, ∃ v, jsonptr.adapted_api.buf_clone_adapted buf = .ok v ∧
    vbytes v = vbytes buf

end JsonptrExtSpec
