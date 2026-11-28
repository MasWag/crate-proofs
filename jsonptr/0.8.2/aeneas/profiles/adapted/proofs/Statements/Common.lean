import JsonptrAdapted
import SpecModelExt
import Specs

/-!
# Shared bridges for the extended-scope contracts (implementation agent)

Adds to the bridges of `Specs` (`bytes`, `vbytes`, `SliceBound`, `ptrOutcome`,
`indexOutcome`, ...) the few views the tier 2-6 contracts need. Nothing here is
a proof obligation.
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrExtSpec

/-- An optional slice as an optional byte list. -/
def obytes (o : Option (Slice U8)) : Option (List Nat) := o.map bytes

/-- An optional pair of slices as an optional pair of byte lists. -/
def opbytes (o : Option (Slice U8 × Slice U8)) : Option (List Nat × List Nat) :=
  o.map (fun p => (bytes p.1, bytes p.2))

/-- An optional vector as an optional byte list. -/
def ovbytes (o : Option (alloc.vec.Vec U8)) : Option (List Nat) := o.map vbytes

/-- `a` is a contiguous part of `b`. -/
def IsInfix (a b : List Nat) : Prop := ∃ p q, b = p ++ a ++ q

/-- The `Pointer` representation invariant on a generated slice. -/
def ValidPtr (s : Slice U8) : Prop := ValidPointer (bytes s)

/-- The `Token` representation invariant on a generated slice. -/
def ValidTok (s : Slice U8) : Prop := ValidEncodedToken (bytes s)

/-- The Rust bound `len ≤ isize::MAX` on a byte list the release builds. -/
def LenBound (l : List Nat) : Prop := (l.length : Int) ≤ Isize.max

/-- A model `Option` result is `some` a valid pointer whenever it is `some`. -/
def ValidPtrOpt (o : Option (List Nat)) : Prop := ∀ r, o = some r → ValidPointer r

/-- Likewise for tokens. -/
def ValidTokOpt (o : Option (List Nat)) : Prop := ∀ r, o = some r → ValidEncodedToken r

/-- Model view of `ComponentAdapted`. -/
def component : jsonptr.adapted_api.ComponentAdapted → Component
  | .Root => .root
  | .Token t => .token (bytes t)

/-- Model view of `BoundAdapted`. -/
def bound : jsonptr.adapted_api.BoundAdapted → Bound
  | .Included n => .included n.val
  | .Excluded n => .excluded n.val
  | .Unbounded => .unbounded

/-- Run `tokens_next_adapted` `k` times, collecting the yielded values. -/
def runTokens : Nat → jsonptr.adapted_api.TokensAdapted → Result (List (Option (Slice U8)))
  | 0, _ => .ok []
  | k + 1, it => do
    let (o, it') ← jsonptr.adapted_api.tokens_next_adapted it
    let os ← runTokens k it'
    .ok (o :: os)

/-- Run `components_next_adapted` `k` times, collecting the yielded values. -/
def runComponents : Nat → jsonptr.adapted_api.ComponentsAdapted →
    Result (List (Option jsonptr.adapted_api.ComponentAdapted))
  | 0, _ => .ok []
  | k + 1, it => do
    let (o, it') ← jsonptr.adapted_api.components_next_adapted it
    let os ← runComponents k it'
    .ok (o :: os)

/-- The first `k` items of a finite sequence followed by `none` forever. -/
def seqThenNone {α : Type} (xs : List α) (k : Nat) : List (Option α) :=
  (xs.map some ++ List.replicate k none).take k

/-- Model view of `core::cmp::Ordering` against `bytesLt`. -/
def OrderingAgrees (o : Ordering) (a b : List Nat) : Prop :=
  match o with
  | .lt => bytesLt a b = true
  | .eq => a = b
  | .gt => bytesLt b a = true

end JsonptrExtSpec
