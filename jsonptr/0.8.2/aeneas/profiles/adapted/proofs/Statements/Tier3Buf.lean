import Statements.Common

/-!
# Tier 3 contracts (specification sections 12-14), adapted bodies

`PointerBuf` is a byte vector. A token argument is its encoded bytes; the
`Into<Token>` conversion is target 2 and is composed in by the caller. Every
final buffer is required to be a valid pointer. The Rust bound
`len ≤ isize::MAX` is assumed only on the buffer the release builds
(`LenBound` of the model result): this is the allocation-representability
premise of the default specification, and the specification allows it here.
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrExtSpec

/-! ## Section 12: construction and mutation -/

/-- `PointerBuf::new`, `root`, `Default`. -/
def BufNewContract : Prop :=
  ∃ v, jsonptr.adapted_api.buf_new_adapted = .ok v ∧ vbytes v = [] ∧ ValidPointer (vbytes v)

/-- `Pointer::to_buf`, `ToOwned::to_owned`. -/
def ToBufContract : Prop :=
  ∀ xs : Slice U8, ValidPtr xs → ∃ v, jsonptr.adapted_api.to_buf_adapted xs = .ok v ∧
    vbytes v = bytes xs ∧ ValidPointer (vbytes v)

/-- `PointerBuf::from_tokens` over encoded tokens; `From<Token>` is the
one-token case. -/
def FromTokensContract : Prop :=
  ∀ ts : Slice (alloc.vec.Vec U8), (∀ t ∈ ts.val, ValidEncodedToken (vbytes t)) →
    LenBound (fromTokens (ts.val.map vbytes)) →
    ∃ v, jsonptr.adapted_api.from_tokens_adapted ts = .ok v ∧
      vbytes v = fromTokens (ts.val.map vbytes) ∧ ValidPointer (vbytes v)

/-- `PointerBuf::push_back`. -/
def PushBackContract : Prop :=
  ∀ (buf : alloc.vec.Vec U8) (t : Slice U8), ValidPointer (vbytes buf) → ValidTok t →
    LenBound (pushBack (vbytes buf) (bytes t)) →
    ∃ v, jsonptr.adapted_api.push_back_adapted buf t = .ok v ∧
      vbytes v = pushBack (vbytes buf) (bytes t) ∧ ValidPointer (vbytes v)

/-- `PointerBuf::push_front`. -/
def PushFrontContract : Prop :=
  ∀ (buf : alloc.vec.Vec U8) (t : Slice U8), ValidPointer (vbytes buf) → ValidTok t →
    LenBound (pushFront (vbytes buf) (bytes t)) →
    ∃ v, jsonptr.adapted_api.push_front_adapted buf t = .ok v ∧
      vbytes v = pushFront (vbytes buf) (bytes t) ∧ ValidPointer (vbytes v)

/-- `PointerBuf::pop_back`: the final buffer and the removed token. -/
def PopBackContract : Prop :=
  ∀ buf : alloc.vec.Vec U8, ValidPointer (vbytes buf) →
    ∃ r v, jsonptr.adapted_api.pop_back_adapted buf = .ok (r, v) ∧
      (vbytes v, ovbytes r) = popBack (vbytes buf) ∧ ValidPointer (vbytes v) ∧
      ValidTokOpt (ovbytes r)

/-- `PointerBuf::pop_front`: the final buffer and the removed token. -/
def PopFrontContract : Prop :=
  ∀ buf : alloc.vec.Vec U8, ValidPointer (vbytes buf) →
    ∃ r v, jsonptr.adapted_api.pop_front_adapted buf = .ok (r, v) ∧
      (vbytes v, ovbytes r) = popFront (vbytes buf) ∧ ValidPointer (vbytes v) ∧
      ValidTokOpt (ovbytes r)

/-- `PointerBuf::append`. -/
def AppendContract : Prop :=
  ∀ (buf : alloc.vec.Vec U8) (other : Slice U8), ValidPointer (vbytes buf) → ValidPtr other →
    LenBound (append (vbytes buf) (bytes other)) →
    ∃ v, jsonptr.adapted_api.append_adapted buf other = .ok v ∧
      vbytes v = append (vbytes buf) (bytes other) ∧ ValidPointer (vbytes v)

/-- `PointerBuf::replace`, for every index up to `usize::MAX`. On error the
buffer is unchanged; success always returns `Some`. -/
def ReplaceContract : Prop :=
  ∀ (buf : alloc.vec.Vec U8) (index : Usize) (t : Slice U8),
    ValidPointer (vbytes buf) → ValidTok t →
    (∀ fin old, replaceToken (vbytes buf) index.val (bytes t) = .ok (fin, old) → LenBound fin) →
    ∃ r v, jsonptr.adapted_api.replace_adapted buf index t = .ok (r, v) ∧
      ValidPointer (vbytes v) ∧
      match r with
      | .Ok none => False
      | .Ok (some old) => replaceToken (vbytes buf) index.val (bytes t) = .ok (vbytes v, vbytes old) ∧
          ValidEncodedToken (vbytes old)
      | .Err e => replaceToken (vbytes buf) index.val (bytes t) = .error ⟨e.index.val, e.count.val⟩ ∧
          vbytes v = vbytes buf

/-- `PointerBuf::clear`. -/
def ClearContract : Prop :=
  ∀ buf : alloc.vec.Vec U8, ∃ v, jsonptr.adapted_api.clear_adapted buf = .ok v ∧ vbytes v = []

/-- `Pointer::with_trailing_token`. -/
def WithTrailingTokenContract : Prop :=
  ∀ xs t : Slice U8, ValidPtr xs → ValidTok t → LenBound (pushBack (bytes xs) (bytes t)) →
    ∃ v, jsonptr.adapted_api.with_trailing_token_adapted xs t = .ok v ∧
      vbytes v = pushBack (bytes xs) (bytes t) ∧ ValidPointer (vbytes v)

/-- `Pointer::with_leading_token`. -/
def WithLeadingTokenContract : Prop :=
  ∀ xs t : Slice U8, ValidPtr xs → ValidTok t → LenBound (pushFront (bytes xs) (bytes t)) →
    ∃ v, jsonptr.adapted_api.with_leading_token_adapted xs t = .ok v ∧
      vbytes v = pushFront (bytes xs) (bytes t) ∧ ValidPointer (vbytes v)

/-- `Pointer::concat`. -/
def ConcatContract : Prop :=
  ∀ xs other : Slice U8, ValidPtr xs → ValidPtr other → LenBound (append (bytes xs) (bytes other)) →
    ∃ v, jsonptr.adapted_api.concat_adapted xs other = .ok v ∧
      vbytes v = append (bytes xs) (bytes other) ∧ ValidPointer (vbytes v)

/-! ## Section 13: parse wrappers -/

/-- Model view of a parse outcome that returns the bytes on success. -/
def ParseOutcome {α : Type} (input : List Nat) (view : α → List Nat) :
    core.result.Result α jsonptr.pointer.ParseError → Prop
  | .Ok v => view v = input ∧ pointerError input = none
  | .Err e => ptrOutcome (.Err e) = some (pointerError input)

/-- `Pointer::parse`. -/
def PointerParseContract : Prop :=
  ∀ s : Slice U8, ∃ r, jsonptr.adapted_api.pointer_parse_adapted s = .ok r ∧
    ParseOutcome (bytes s) bytes r

/-- `PointerBuf::try_from(&str)` and `PointerBuf::from_str`. -/
def BufTryFromStrContract : Prop :=
  ∀ s : Slice U8, ∃ r, jsonptr.adapted_api.buf_try_from_str_adapted s = .ok r ∧
    ParseOutcome (bytes s) vbytes r

/-- `PointerBuf::try_from(String)`. -/
def BufTryFromStringContract : Prop :=
  ∀ s : alloc.vec.Vec U8, ∃ r, jsonptr.adapted_api.buf_try_from_string_adapted s = .ok r ∧
    ParseOutcome (vbytes s) vbytes r

/-- `PointerBuf::parse`: on failure the report's original error is the target 1
error and its subject is the unchanged input. -/
def BufParseContract : Prop :=
  ∀ s : alloc.vec.Vec U8, ∃ r, jsonptr.adapted_api.buf_parse_adapted s = .ok r ∧
    match r with
    | .Ok v => vbytes v = vbytes s ∧ pointerError (vbytes s) = none
    | .Err rep => ptrOutcome (.Err rep.source) = some (pointerError (vbytes s)) ∧
        rep.subject = s

/-- `Pointer::from_static`: success exactly when `pointerError` is `none`, with
the input returned; otherwise the documented panic, a failing `assert!`, which
the Aeneas model reports as `Error.assertionFailure`. Not a total contract. -/
def FromStaticContract : Prop :=
  ∀ s : Slice U8,
    (pointerError (bytes s) = none → jsonptr.adapted_api.from_static_adapted s = .ok s) ∧
    (pointerError (bytes s) ≠ none → jsonptr.adapted_api.from_static_adapted s = .fail .assertionFailure)

/-! ## Section 14: small token and index items -/

/-- `Token::encoded`, `into_encoded`. -/
def TokenEncodedContract : Prop :=
  ∀ t : Slice U8, ValidTok t → ∃ r, jsonptr.adapted_api.token_encoded_adapted t = .ok r ∧
    bytes r = bytes t ∧ ValidTok r

/-- `Token::into_owned`, `to_owned`, `Clone`, `From<&Token>`. -/
def TokenToOwnedContract : Prop :=
  ∀ t : Slice U8, ValidTok t → ∃ v, jsonptr.adapted_api.token_to_owned_adapted t = .ok v ∧
    vbytes v = bytes t ∧ ValidEncodedToken (vbytes v)

/-- `Token::is_next`. -/
def IsNextContract : Prop :=
  ∀ t : Slice U8, ValidTok t → ∃ b, jsonptr.adapted_api.is_next_adapted t = .ok b ∧
    b = isNext (bytes t)

/-- `StringOrToken::from(String)` then `deref`. -/
def SotStringContract : Prop :=
  ∀ v : alloc.vec.Vec U8, ∃ s r, jsonptr.adapted_api.sot_from_string_adapted v = .ok s ∧
    jsonptr.adapted_api.sot_deref_adapted s = .ok r ∧ bytes r = vbytes v

/-- `StringOrToken::from(Token)` then `deref`: the token's encoded bytes. -/
def SotTokenContract : Prop :=
  ∀ v : alloc.vec.Vec U8, ValidEncodedToken (vbytes v) →
    ∃ s r, jsonptr.adapted_api.sot_from_token_adapted v = .ok s ∧
      jsonptr.adapted_api.sot_deref_adapted s = .ok r ∧ bytes r = vbytes v

end JsonptrExtSpec
