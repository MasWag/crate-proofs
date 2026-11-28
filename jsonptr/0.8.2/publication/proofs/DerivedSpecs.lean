import Jsonptr


/-!
# Contracts for release items that extract unchanged (default-profile additions)

The subject is the generated model of the UNCHANGED release source
(`Generated/default/JsonptrDerived.lean`). Section 21 (derived `Clone`,
`PartialEq`, `Ord`; `Index::from`; `Pointer::as_str`), section 18 (the
`ParseError` accessors, `InvalidCharacterError::offset`), section 19
(`Diagnostic::url`, `Label::new`) and section 20 (`Report` accessors).
-/

open Aeneas Aeneas.Std


namespace JsonptrDerivedSpec

open jsonptr

/-! ## Section 21 -/

def IndexEqContract : Prop :=
  ∀ a b : index.Index, ∃ r, index.Index.Insts.CoreCmpPartialEqIndex.eq a b = .ok r ∧ (r = true ↔ a = b)

def IndexCloneContract : Prop := ∀ a : index.Index, index.Index.Insts.CoreCloneClone.clone a = .ok a

def IndexFromContract : Prop :=
  ∀ n : Usize, index.Index.Insts.CoreConvertFromUsize.from n = .ok (.Num n)

/-- `Index` order: `Num` by value, every `Num` before `Next`. -/
def indexOrd : index.Index → index.Index → Ordering
  | .Num a, .Num b => compare a.val b.val
  | .Num _, .Next => .lt
  | .Next, .Num _ => .gt
  | .Next, .Next => .eq

def IndexCmpContract : Prop :=
  ∀ a b : index.Index, index.Index.Insts.CoreCmpOrd.cmp a b = .ok (indexOrd a b) ∧
    index.Index.Insts.CoreCmpPartialOrdIndex.partial_cmp a b = .ok (some (indexOrd a b))

def OobEqCloneContract : Prop :=
  ∀ a b : index.OutOfBoundsError,
    index.OutOfBoundsError.Insts.CoreCloneClone.clone a = .ok a ∧
    ∃ r, index.OutOfBoundsError.Insts.CoreCmpPartialEqOutOfBoundsError.eq a b = .ok r ∧ (r = true ↔ a = b)

def IceContract : Prop :=
  ∀ a b : index.InvalidCharacterError,
    index.InvalidCharacterError.Insts.CoreCloneClone.clone a = .ok a ∧
    index.InvalidCharacterError.impl.offset a = .ok a.offset ∧
    ∃ r, index.InvalidCharacterError.Insts.CoreCmpPartialEqInvalidCharacterError.eq a b = .ok r ∧
      (r = true ↔ a = b)

def InvalidEncodingContract : Prop :=
  ∀ a b : token.InvalidEncoding,
    token.InvalidEncoding.Insts.CoreCloneClone.clone a = .ok a ∧
    ∃ r, token.InvalidEncoding.Insts.CoreCmpPartialEqInvalidEncoding.eq a b = .ok r ∧ (r = true ↔ a = b)

def EncodingErrorEqContract : Prop :=
  ∀ a b : token.EncodingError,
    ∃ r, token.EncodingError.Insts.CoreCmpPartialEqEncodingError.eq a b = .ok r ∧ (r = true ↔ a = b)

def ParseErrorEqContract : Prop :=
  ∀ a b : pointer.ParseError,
    ∃ r, pointer.ParseError.Insts.CoreCmpPartialEqParseError.eq a b = .ok r ∧ (r = true ↔ a = b)

def ReplaceErrorEqContract : Prop :=
  ∀ a b : pointer.ReplaceError,
    ∃ r, pointer.ReplaceError.Insts.CoreCmpPartialEqReplaceError.eq a b = .ok r ∧ (r = true ↔ a = b)

def AsStrContract : Prop := ∀ p : pointer.Pointer, pointer.Pointer.as_str p = .ok p

/-! ## Section 18 -/

def peOff : pointer.ParseError → Usize
  | .NoLeadingSlash => 0#usize
  | .InvalidEncoding d _ => d

def peSrc : pointer.ParseError → Usize
  | .NoLeadingSlash => 0#usize
  | .InvalidEncoding _ s => s.offset

def peIsNls : pointer.ParseError → Bool
  | .NoLeadingSlash => true
  | .InvalidEncoding _ _ => false

def ParseErrorAccessorsContract : Prop :=
  ∀ e : pointer.ParseError,
    pointer.ParseError.offset e = .ok (peOff e) ∧
    pointer.ParseError.pointer_offset e = .ok (peOff e) ∧
    pointer.ParseError.source_offset e = .ok (peSrc e) ∧
    pointer.ParseError.is_no_leading_slash e = .ok (peIsNls e) ∧
    pointer.ParseError.is_no_leading_backslash e = .ok (peIsNls e) ∧
    pointer.ParseError.is_invalid_encoding e = .ok (!peIsNls e)

/-- `complete_offset` for every error value whose sum fits. -/
def CompleteOffsetContract : Prop :=
  ∀ e : pointer.ParseError, (peOff e).val + (peSrc e).val ≤ Usize.max →
    ∃ n, pointer.ParseError.complete_offset e = .ok n ∧ n.val = (peOff e).val + (peSrc e).val

/-- INTENDED total success of `complete_offset`. Refuted (N7). -/
def CompleteOffsetTotalContract : Prop :=
  ∀ e : pointer.ParseError, ∃ n, pointer.ParseError.complete_offset e = .ok n

/-! ## Sections 19 and 20 -/

/-- `Diagnostic::url` returns the docs.rs address of each error type, one
contract per type. Intended addresses: `ParseError` is an enum at the crate root
(refuted, N10: the release returns `struct.ParseError.html`); `EncodingError`
is a struct at the root; `assign::Error` and `resolve::Error` live in their
modules (refuted for `resolve`, N3); `ParseIndexError` lives in `jsonptr::index`
and is not re-exported (refuted, N9). -/
def ParseErrorUrlContract : Prop :=
  pointer.ParseError.Insts.JsonptrDiagnosticDiagnosticStringStr.url =
    .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/enum.ParseError.html")

def EncodingErrorUrlContract : Prop :=
  token.EncodingError.Insts.JsonptrDiagnosticDiagnosticStringStr.url =
    .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/struct.EncodingError.html")

def AssignErrorUrlContract : Prop :=
  assign.Error.Insts.JsonptrDiagnosticDiagnosticPointerBufPointer.url =
    .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/assign/enum.Error.html")

def ResolveErrorUrlContract : Prop :=
  resolve.Error.Insts.JsonptrDiagnosticDiagnosticPointerBufPointer.url =
    .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/resolve/enum.Error.html")

def ParseIndexErrorUrlContract : Prop :=
  index.ParseIndexError.Insts.JsonptrDiagnosticDiagnosticStringOrTokenStr.url =
    .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/index/enum.ParseIndexError.html")

/-- Behaviour record: the address `ParseIndexError::url` returns (N9). -/
def ParseIndexErrorUrlRecord : Prop :=
  index.ParseIndexError.Insts.JsonptrDiagnosticDiagnosticStringOrTokenStr.url =
    .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/enum.ParseIndexError.html")

def LabelNewContract : Prop :=
  ∀ (text : String) (o l : Usize), ∃ lab, diagnostic.Label.new text o l = .ok lab ∧
    lab.text = text ∧ lab.offset = o ∧ lab.len = l

def ReportAccessorsContract : Prop :=
  ∀ {T S U : Type} (r : diagnostic.Report T S U),
    diagnostic.Report.original r = .ok r.source ∧
    diagnostic.Report.into_original r = .ok r.source ∧
    diagnostic.Report.decompose r = .ok (r.source, r.subject)

end JsonptrDerivedSpec
