import Statements.Common

/-!
# Tier 2 contracts (specification sections 8-11), adapted bodies

Each proposition is the total-success contract of one adapted function in
`adapted_api.rs`, stated against the specification model (`SpecModelExt`).
A pointer argument satisfies `ValidPointer`; every pointer or token result is
required to satisfy its invariant. The propositions are proved, if at all, in
`ExtProofs.*`. Refuted contracts (JSONPTR-001, JSONPTR-002) are stated as
intended; their refutations are separate theorems.
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrExtSpec

/-! ## Section 8: tokens, navigation, components -/

/-- `Tokens::next` after `Pointer::tokens`: the yielded sequence is
`encodedTokens xs`, then `None` forever; every yielded token is valid. -/
def TokensContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ it, jsonptr.adapted_api.tokens_adapted xs = .ok it ∧
    ∀ k, ∃ os, runTokens k it = .ok os ∧
      os.map (Option.map bytes) = seqThenNone (encodedTokens (bytes xs)) k ∧
      ∀ t, some t ∈ os → ValidTok t

/-- `Pointer::count`. -/
def CountContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ n, jsonptr.adapted_api.count_adapted xs = .ok n ∧
    n.val = count (bytes xs)

/-- `Pointer::front`, `first`. -/
def FrontContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ r, jsonptr.adapted_api.front_adapted xs = .ok r ∧
    obytes r = front (bytes xs) ∧ ValidTokOpt (obytes r)

/-- `Pointer::back`, `last`. -/
def BackContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ r, jsonptr.adapted_api.back_adapted xs = .ok r ∧
    obytes r = back (bytes xs) ∧ ValidTokOpt (obytes r)

/-- `Pointer::split_back`: the parent and the last token; the parent is a valid
pointer and `xs = parent ++ "/" ++ token`. -/
def SplitBackContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ r, jsonptr.adapted_api.split_back_adapted xs = .ok r ∧
    opbytes r = splitBack (bytes xs) ∧
    ∀ h t, r = some (h, t) → ValidPtr h ∧ ValidTok t ∧ bytes xs = bytes h ++ 47 :: bytes t

/-- `Pointer::parent`. -/
def ParentContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ r, jsonptr.adapted_api.parent_adapted xs = .ok r ∧
    obytes r = parent (bytes xs) ∧ ValidPtrOpt (obytes r)

/-- `Pointer::get` with a `usize`, for every index up to `usize::MAX`. -/
def GetIndexContract : Prop :=
  ∀ (xs : Slice U8) (i : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_index_adapted xs i = .ok r ∧
      obytes r = getToken (bytes xs) i.val ∧ ValidTokOpt (obytes r)

/-- `Components::next` after `From<&Pointer>`: `Root`, then each token, then
`None` forever. -/
def ComponentsContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ it, jsonptr.adapted_api.components_adapted xs = .ok it ∧
    ∀ k, ∃ os, runComponents k it = .ok os ∧
      os.map (Option.map component) = seqThenNone (components (bytes xs)) k ∧
      ∀ t, some (jsonptr.adapted_api.ComponentAdapted.Token t) ∈ os → ValidTok t

/-- `From<Token> for Component`. -/
def ComponentFromTokenContract : Prop :=
  ∀ t : Slice U8, ValidTok t → ∃ c, jsonptr.adapted_api.component_from_token_adapted t = .ok c ∧
    component c = .token (bytes t)

/-! ## Section 9: range indexing -/

/-- A range result: equal to the model, a valid pointer, and a contiguous part
of the input. -/
def RangeResult (xs : Slice U8) (r : Option (Slice U8)) (m : Option (List Nat)) : Prop :=
  obytes r = m ∧ ValidPtrOpt (obytes r) ∧ ∀ v, r = some v → IsInfix (bytes v) (bytes xs)

def GetRangeContract : Prop :=
  ∀ (xs : Slice U8) (s e : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_range_adapted xs s e = .ok r ∧
      RangeResult xs r (getRange (bytes xs) s.val e.val)

def GetRangeFromContract : Prop :=
  ∀ (xs : Slice U8) (s : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_range_from_adapted xs s = .ok r ∧
      RangeResult xs r (getRangeFrom (bytes xs) s.val)

def GetRangeToContract : Prop :=
  ∀ (xs : Slice U8) (e : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_range_to_adapted xs e = .ok r ∧
      RangeResult xs r (getRangeTo (bytes xs) e.val)

def GetRangeInclusiveContract : Prop :=
  ∀ (xs : Slice U8) (s e : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_range_inclusive_adapted xs s e = .ok r ∧
      RangeResult xs r (getRangeIncl (bytes xs) s.val e.val)

def GetRangeToInclusiveContract : Prop :=
  ∀ (xs : Slice U8) (e : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_range_to_inclusive_adapted xs e = .ok r ∧
      RangeResult xs r (getRangeToIncl (bytes xs) e.val)

def GetRangeFullContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_range_full_adapted xs = .ok r ∧
      RangeResult xs r (some (bytes xs))

/-- INTENDED `(Bound, Bound)` contract, for every pair of bounds. Refuted for
the release at `Excluded(usize::MAX)` (JSONPTR-002). -/
def GetBoundsContract : Prop :=
  ∀ (xs : Slice U8) (s e : jsonptr.adapted_api.BoundAdapted), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.get_bounds_adapted xs s e = .ok r ∧
      RangeResult xs r (getBounds (bytes xs) (bound s) (bound e))

/-- Behaviour record (not a contract): the intended contract for every start
other than `Excluded(usize::MAX)`. -/
def GetBoundsExceptMaxRecord : Prop :=
  ∀ (xs : Slice U8) (s e : jsonptr.adapted_api.BoundAdapted), ValidPtr xs →
    (∀ n, s = .Excluded n → n.val < Usize.max) →
    ∃ r, jsonptr.adapted_api.get_bounds_adapted xs s e = .ok r ∧
      RangeResult xs r (getBounds (bytes xs) (bound s) (bound e))

/-! ## Section 10: byte split -/

def SplitAtOffsetContract : Prop :=
  ∀ (xs : Slice U8) (off : Usize), ValidPtr xs →
    ∃ r, jsonptr.adapted_api.split_at_offset_adapted xs off = .ok r ∧
      opbytes r = splitAtOffset (bytes xs) off.val ∧
      ∀ h t, r = some (h, t) → ValidPtr h ∧ ValidPtr t

/-! ## Section 11: comparison and prefix operations -/

def StartsWithContract : Prop :=
  ∀ xs other : Slice U8, ValidPtr xs → ValidPtr other →
    ∃ b, jsonptr.adapted_api.starts_with_adapted xs other = .ok b ∧
      b = startsWith (bytes xs) (bytes other)

def EndsWithContract : Prop :=
  ∀ xs other : Slice U8, ValidPtr xs → ValidPtr other →
    ∃ b, jsonptr.adapted_api.ends_with_adapted xs other = .ok b ∧
      b = endsWith (bytes xs) (bytes other)

def StripSuffixContract : Prop :=
  ∀ xs suf : Slice U8, ValidPtr xs → ValidPtr suf →
    ∃ r, jsonptr.adapted_api.strip_suffix_adapted xs suf = .ok r ∧
      obytes r = stripSuffix (bytes xs) (bytes suf) ∧ ValidPtrOpt (obytes r)

/-- INTENDED `strip_prefix` contract. Refuted for the release (JSONPTR-001). -/
def StripPrefixContract : Prop :=
  ∀ xs pre : Slice U8, ValidPtr xs → ValidPtr pre →
    ∃ r, jsonptr.adapted_api.strip_prefix_adapted xs pre = .ok r ∧
      obytes r = stripPrefix (bytes xs) (bytes pre) ∧ ValidPtrOpt (obytes r)

/-- Behaviour record (not a contract): the intended contract holds whenever
`starts_with` holds. -/
def StripPrefixWhenStartsWithRecord : Prop :=
  ∀ xs pre : Slice U8, ValidPtr xs → ValidPtr pre → startsWith (bytes xs) (bytes pre) = true →
    ∃ r, jsonptr.adapted_api.strip_prefix_adapted xs pre = .ok r ∧
      obytes r = stripPrefix (bytes xs) (bytes pre) ∧ ValidPtrOpt (obytes r)

def IntersectionContract : Prop :=
  ∀ xs other : Slice U8, ValidPtr xs → ValidPtr other →
    ∃ r, jsonptr.adapted_api.intersection_adapted xs other = .ok r ∧
      bytes r = intersection (bytes xs) (bytes other) ∧ ValidPtr r

end JsonptrExtSpec
