import Statements.Common

/-!
# Tier 5 contracts (specification sections 18-19), adapted bodies (subset)

Covered here: `ParseError::invalid_encoding_len`, `ParseError::labels`,
`EncodingError::labels` (span only; the fixed label text is not modelled) and
the six `resolve::Error` accessors over the adapted error type. The release
`ParseError` accessors and `Diagnostic::url` extract unchanged; their
contracts are in `Statements.DefaultDerived`. `ParseIndexError::labels`,
`resolve::Error::labels`, `assign::Error::labels`, the `assign::Error`
accessors, `Report` and `Diagnose` are not yet stated (see the ledger).
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrExtSpec

/-- INTENDED `invalid_encoding_len` for an error produced by parsing `subject`.
Refuted for the release (JSONPTR-003). -/
def InvalidEncodingLenContract : Prop :=
  ∀ (e : jsonptr.pointer.ParseError) (subject : Slice U8) (pe : PtrError),
    pointerError (bytes subject) = some pe → ptrOutcome (.Err e) = some (some pe) →
    ∃ n, jsonptr.adapted_api.invalid_encoding_len_adapted e subject = .ok n ∧
      n.val = invalidEncodingLen pe (bytes subject)

/-- INTENDED total success of `invalid_encoding_len` on every error value and
subject. Refuted for the release (N5: the empty subject underflows). -/
def InvalidEncodingLenTotalContract : Prop :=
  ∀ (e : jsonptr.pointer.ParseError) (subject : Slice U8),
    ∃ n, jsonptr.adapted_api.invalid_encoding_len_adapted e subject = .ok n

/-- Behaviour record (not a contract): on a nonempty subject the release
computes `invalidEncodingLenRelease`. -/
def InvalidEncodingLenReleaseRecord : Prop :=
  ∀ (e : jsonptr.pointer.ParseError) (subject : Slice U8) (pe : PtrError),
    bytes subject ≠ [] → ptrOutcome (.Err e) = some (some pe) →
    ∃ n, jsonptr.adapted_api.invalid_encoding_len_adapted e subject = .ok n ∧
      n.val = invalidEncodingLenRelease pe (bytes subject)

/-- INTENDED `ParseError::labels` for an error produced by parsing `subject`:
one label `ptrErrLabel`. Refuted wherever the length is (JSONPTR-003). -/
def ParseErrorLabelContract : Prop :=
  ∀ (e : jsonptr.pointer.ParseError) (subject : Slice U8) (pe : PtrError),
    pointerError (bytes subject) = some pe → ptrOutcome (.Err e) = some (some pe) →
    ∃ sp, jsonptr.adapted_api.parse_error_label_adapted e subject = .ok sp ∧
      (⟨sp.offset.val, sp.len.val⟩ : Span) = ptrErrLabel pe (bytes subject)

/-- `EncodingError::labels` for every error value with offset at least 1 when
the source is `Tilde`; for an error produced by `from_encoded` on `subject`
the span lies inside the subject. -/
def EncodingErrorLabelContract : Prop :=
  ∀ (e : jsonptr.token.EncodingError) (subject : Slice U8),
    (e.source = .Tilde → 1 ≤ e.offset.val) →
    ∃ sp, jsonptr.adapted_api.encoding_error_label_adapted e subject = .ok sp ∧
      (⟨sp.offset.val, sp.len.val⟩ : Span) = encErrLabel (encError e) (bytes subject) ∧
      (firstEncError (bytes subject) = some (encError e) →
        sp.offset.val + sp.len.val ≤ (bytes subject).length)

/-- INTENDED total success of `EncodingError::labels` on every error value.
Refuted for the release (N8: offset 0, `Tilde`, empty subject). -/
def EncodingErrorLabelTotalContract : Prop :=
  ∀ (e : jsonptr.token.EncodingError) (subject : Slice U8),
    ∃ sp, jsonptr.adapted_api.encoding_error_label_adapted e subject = .ok sp

/-- The stored `position` and `offset` of an adapted resolve error. -/
def resolveErrFields : jsonptr.resolve.ResolveErrorAdapted → Usize × Usize
  | .FailedToParseIndex p o _ => (p, o)
  | .OutOfBounds p o _ => (p, o)
  | .NotFound p o => (p, o)
  | .Unreachable p o => (p, o)

/-- The variant of an adapted resolve error: 0 `FailedToParseIndex`,
1 `OutOfBounds`, 2 `NotFound`, 3 `Unreachable`. -/
def resolveErrVariant : jsonptr.resolve.ResolveErrorAdapted → Nat
  | .FailedToParseIndex .. => 0
  | .OutOfBounds .. => 1
  | .NotFound .. => 2
  | .Unreachable .. => 3

/-- `resolve::Error::offset`, `position` and the four `is_*` classifiers. -/
def ResolveErrorAccessorsContract : Prop :=
  ∀ e : jsonptr.resolve.ResolveErrorAdapted,
    jsonptr.adapted_api.resolve_err.resolve_error_offset_adapted e = .ok (resolveErrFields e).2 ∧
    jsonptr.adapted_api.resolve_err.resolve_error_position_adapted e = .ok (resolveErrFields e).1 ∧
    jsonptr.adapted_api.resolve_err.resolve_error_is_unreachable_adapted e =
      .ok (decide (resolveErrVariant e = 3)) ∧
    jsonptr.adapted_api.resolve_err.resolve_error_is_not_found_adapted e =
      .ok (decide (resolveErrVariant e = 2)) ∧
    jsonptr.adapted_api.resolve_err.resolve_error_is_out_of_bounds_adapted e =
      .ok (decide (resolveErrVariant e = 1)) ∧
    jsonptr.adapted_api.resolve_err.resolve_error_is_failed_to_parse_index_adapted e =
      .ok (decide (resolveErrVariant e = 0))

/-- Model view of an optional span. -/
def ospan (o : Option jsonptr.adapted_api.SpanAdapted) : Option Span :=
  o.map (fun sp => ⟨sp.offset.val, sp.len.val⟩)

/-- INTENDED `ParseIndexError::labels` for an error produced by parsing
`subject`: `IndexErrLabelPost`. Refuted for the release (N1, N2). -/
def ParseIndexErrorLabelContract : Prop :=
  ∀ (e : jsonptr.index.ParseIndexErrorAdapted) (subject : Slice U8),
    parseIndex Usize.max (bytes subject) = .error (indexError e) →
    ∃ o, jsonptr.adapted_api.parse_index_error_label_adapted e subject = .ok o ∧
      IndexErrLabelPost (indexError e) (bytes subject) (ospan o)

/-- `resolve::Error::labels` for errors with `offset < usize::MAX` on a valid
origin: `tokenErrLabel`. -/
def ResolveErrorLabelContract : Prop :=
  ∀ (e : jsonptr.resolve.ResolveErrorAdapted) (origin : Slice U8), ValidPtr origin →
    (resolveErrFields e).2.val < Usize.max →
    ∃ o, jsonptr.adapted_api.resolve_err.resolve_error_label_adapted e origin = .ok o ∧
      ospan o = tokenErrLabel (resolveErrFields e).1.val (resolveErrFields e).2.val (bytes origin)

/-- INTENDED total success of `resolve::Error::labels`. Refuted (N6). -/
def ResolveErrorLabelTotalContract : Prop :=
  ∀ (e : jsonptr.resolve.ResolveErrorAdapted) (origin : Slice U8), ValidPtr origin →
    ∃ o, jsonptr.adapted_api.resolve_err.resolve_error_label_adapted e origin = .ok o

def assignErrFields : jsonptr.adapted_api.doc_mut.AssignErrorAdapted → Usize × Usize
  | .FailedToParseIndex p o _ => (p, o)
  | .OutOfBounds p o _ => (p, o)

/-- `assign::Error::position`, `offset`, `is_out_of_bounds`, `is_failed_to_parse_index`. -/
def AssignErrorAccessorsContract : Prop :=
  ∀ e : jsonptr.adapted_api.doc_mut.AssignErrorAdapted,
    jsonptr.adapted_api.doc_mut.assign_error_position_adapted e = .ok (assignErrFields e).1 ∧
    jsonptr.adapted_api.doc_mut.assign_error_offset_adapted e = .ok (assignErrFields e).2 ∧
    jsonptr.adapted_api.doc_mut.assign_error_is_out_of_bounds_adapted e =
      .ok (match e with | .OutOfBounds .. => true | _ => false) ∧
    jsonptr.adapted_api.doc_mut.assign_error_is_failed_to_parse_index_adapted e =
      .ok (match e with | .FailedToParseIndex .. => true | _ => false)

/-- `assign::Error::labels` for errors with `offset < usize::MAX`: `tokenErrLabel`. -/
def AssignErrorLabelContract : Prop :=
  ∀ (e : jsonptr.adapted_api.doc_mut.AssignErrorAdapted) (origin : Slice U8), ValidPtr origin →
    (assignErrFields e).2.val < Usize.max →
    ∃ o, jsonptr.adapted_api.doc_mut.assign_error_label_adapted e origin = .ok o ∧
      ospan o = tokenErrLabel (assignErrFields e).1.val (assignErrFields e).2.val (bytes origin)

/-- INTENDED total success of `assign::Error::labels`. Refuted (N6). -/
def AssignErrorLabelTotalContract : Prop :=
  ∀ (e : jsonptr.adapted_api.doc_mut.AssignErrorAdapted) (origin : Slice U8), ValidPtr origin →
    ∃ o, jsonptr.adapted_api.doc_mut.assign_error_label_adapted e origin = .ok o

/-- `Result::diagnose` for a `ParseError` result: `Ok` passes, `Err e` becomes the
report of `e` and the subject. -/
def DiagnoseContract : Prop :=
  ∀ (r : core.result.Result Usize jsonptr.pointer.ParseError) (subject : alloc.vec.Vec U8),
    jsonptr.adapted_api.diagnose_parse_adapted r subject =
      .ok (match r with | .Ok t => .Ok t | .Err e => .Err { source := e, subject := subject })

end JsonptrExtSpec
