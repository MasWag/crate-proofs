import Statements.Common

/-!
# Tier 4 contracts (specification sections 15-17), adapted bodies

Over the local document type `DocAdapted` of target 7 and its abstraction
`toTree`. The pointer argument is the rendering of its decoded keys
(`render keys = bytes ptr`, the premise of target 7) with `SliceBound ptr`.
The JSON root replacement `Value::Null` is `Leaf 0`; TOML's empty table is
`Object []`. Statements of exact final documents; member order is the model's.
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrExtSpec

def assignError : jsonptr.adapted_api.doc_mut.AssignErrorAdapted → AssignError
  | .FailedToParseIndex p o e => .failedToParseIndex p.val o.val (indexError e)
  | .OutOfBounds p o e => .outOfBounds p.val o.val ⟨e.length.val, e.index.val⟩

/-- Section 15, `ResolveMut::resolve_mut`: the outcome equals target 7's; writing
`new` through the returned reference gives `replaceAt`; writing back the node
read leaves the document unchanged; on error the document is unchanged. -/
def ResolveMutContract : Prop :=
  ∀ (doc : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (keys : List (List Nat)),
    render keys = bytes ptr → SliceBound ptr →
    ∃ r back, jsonptr.adapted_api.doc_mut.resolve_mut_adapted doc ptr = .ok (r, back) ∧
      resolveOutcome r = resolve Usize.max (toTree doc) keys ∧
      (∀ n, r = .Ok n → back (.Ok n) = doc ∧
        ∀ new, replaceAt Usize.max (toTree doc) keys (toTree new) = some (toTree (back (.Ok new)))) ∧
      (∀ e x, r = .Err e → back x = doc)

-- Every array and object has fewer than `usize::MAX` entries: the
-- allocation-representability premise (`Vec::push` must not overflow the length),
-- like `LenBound`.
mutual
/-- Bound on one node. -/
def TreeBound : Tree → Prop
  | .leaf _ => True
  | .arr items => items.length < Usize.max ∧ TreesBound items
  | .obj ms => ms.length < Usize.max ∧ MembersBound ms
def TreesBound : List Tree → Prop
  | [] => True
  | c :: cs => TreeBound c ∧ TreesBound cs
def MembersBound : List (List Nat × Tree) → Prop
  | [] => True
  | (_, c) :: cs => TreeBound c ∧ MembersBound cs
end

/-- Section 16, `Assign::assign`: outcome and final document equal `assign`. -/
def AssignContract : Prop :=
  ∀ (doc : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (keys : List (List Nat))
    (v : jsonptr.resolve.DocAdapted),
    render keys = bytes ptr → SliceBound ptr → TreeBound (toTree doc) →
    ∃ r doc', jsonptr.adapted_api.doc_mut.assign_adapted doc ptr v = .ok (r, doc') ∧
      match r with
      | .Ok old => assign Usize.max (toTree doc) keys (toTree v) = .ok (toTree doc', old.map toTree)
      | .Err e => assign Usize.max (toTree doc) keys (toTree v) = .error (assignError e) ∧ doc' = doc

/-- Section 17, `Delete::delete` for JSON (root replacement `Value::Null`). -/
def DeleteJsonContract : Prop :=
  ∀ (doc : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (keys : List (List Nat)),
    render keys = bytes ptr → SliceBound ptr →
    ∃ r doc', jsonptr.adapted_api.doc_mut.delete_json_adapted doc ptr = .ok (r, doc') ∧
      (toTree doc', r.map toTree) = delete Usize.max (.leaf 0) (toTree doc) keys

/-- Section 17, `Delete::delete` for TOML (root replacement an empty table). -/
def DeleteTomlContract : Prop :=
  ∀ (doc : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (keys : List (List Nat)),
    render keys = bytes ptr → SliceBound ptr →
    ∃ r doc', jsonptr.adapted_api.doc_mut.delete_toml_adapted doc ptr = .ok (r, doc') ∧
      (toTree doc', r.map toTree) = delete Usize.max (.obj []) (toTree doc) keys

end JsonptrExtSpec
