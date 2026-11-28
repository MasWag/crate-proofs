import DerivedProofs

/-!
# Per-API projections for publication

Some default-profile theorems state one contract for several APIs. A proofs.rs
mapping names one API per theorem, so each theorem below restates exactly one
API's part of the named default-profile theorem and proves it by projection.
No assumption or model is added.
-/

open Aeneas Aeneas.Std
open jsonptr JsonptrDerivedSpec

namespace JsonptrPublication

/-- `Ord::cmp` part of `JsonptrDerivedProofs.indexCmp`. -/
theorem indexOrdCmp (a b : index.Index) :
    index.Index.Insts.CoreCmpOrd.cmp a b = .ok (indexOrd a b) :=
  (JsonptrDerivedProofs.indexCmp a b).1

/-- `PartialOrd::partial_cmp` part of `JsonptrDerivedProofs.indexCmp`. -/
theorem indexPartialCmp (a b : index.Index) :
    index.Index.Insts.CoreCmpPartialOrdIndex.partial_cmp a b = .ok (some (indexOrd a b)) :=
  (JsonptrDerivedProofs.indexCmp a b).2

/-- `Clone::clone` part of `JsonptrDerivedProofs.oobEqClone`. -/
theorem outOfBoundsClone (a : index.OutOfBoundsError) :
    index.OutOfBoundsError.Insts.CoreCloneClone.clone a = .ok a :=
  (JsonptrDerivedProofs.oobEqClone a a).1

/-- `PartialEq::eq` part of `JsonptrDerivedProofs.oobEqClone`. -/
theorem outOfBoundsEq (a b : index.OutOfBoundsError) :
    ∃ r, index.OutOfBoundsError.Insts.CoreCmpPartialEqOutOfBoundsError.eq a b = .ok r ∧
      (r = true ↔ a = b) :=
  (JsonptrDerivedProofs.oobEqClone a b).2

/-- `Clone::clone` part of `JsonptrDerivedProofs.ice`. -/
theorem invalidCharacterClone (a : index.InvalidCharacterError) :
    index.InvalidCharacterError.Insts.CoreCloneClone.clone a = .ok a :=
  (JsonptrDerivedProofs.ice a a).1

/-- `InvalidCharacterError::offset` part of `JsonptrDerivedProofs.ice`. -/
theorem invalidCharacterOffset (a : index.InvalidCharacterError) :
    index.InvalidCharacterError.impl.offset a = .ok a.offset :=
  (JsonptrDerivedProofs.ice a a).2.1

/-- `PartialEq::eq` part of `JsonptrDerivedProofs.ice`. -/
theorem invalidCharacterEq (a b : index.InvalidCharacterError) :
    ∃ r, index.InvalidCharacterError.Insts.CoreCmpPartialEqInvalidCharacterError.eq a b = .ok r ∧
      (r = true ↔ a = b) :=
  (JsonptrDerivedProofs.ice a b).2.2

/-- `Clone::clone` part of `JsonptrDerivedProofs.invalidEncoding`. -/
theorem invalidEncodingClone (a : token.InvalidEncoding) :
    token.InvalidEncoding.Insts.CoreCloneClone.clone a = .ok a :=
  (JsonptrDerivedProofs.invalidEncoding a a).1

/-- `PartialEq::eq` part of `JsonptrDerivedProofs.invalidEncoding`. -/
theorem invalidEncodingEq (a b : token.InvalidEncoding) :
    ∃ r, token.InvalidEncoding.Insts.CoreCmpPartialEqInvalidEncoding.eq a b = .ok r ∧
      (r = true ↔ a = b) :=
  (JsonptrDerivedProofs.invalidEncoding a b).2

/-- `ParseError::offset` part of `JsonptrDerivedProofs.parseErrorAccessors`. -/
theorem parseErrorOffset (e : pointer.ParseError) :
    pointer.ParseError.offset e = .ok (peOff e) :=
  (JsonptrDerivedProofs.parseErrorAccessors e).1

/-- `ParseError::pointer_offset` part of `JsonptrDerivedProofs.parseErrorAccessors`. -/
theorem parseErrorPointerOffset (e : pointer.ParseError) :
    pointer.ParseError.pointer_offset e = .ok (peOff e) :=
  (JsonptrDerivedProofs.parseErrorAccessors e).2.1

/-- `ParseError::source_offset` part of `JsonptrDerivedProofs.parseErrorAccessors`. -/
theorem parseErrorSourceOffset (e : pointer.ParseError) :
    pointer.ParseError.source_offset e = .ok (peSrc e) :=
  (JsonptrDerivedProofs.parseErrorAccessors e).2.2.1

/-- `ParseError::is_no_leading_slash` part of `JsonptrDerivedProofs.parseErrorAccessors`. -/
theorem parseErrorIsNoLeadingSlash (e : pointer.ParseError) :
    pointer.ParseError.is_no_leading_slash e = .ok (peIsNls e) :=
  (JsonptrDerivedProofs.parseErrorAccessors e).2.2.2.1

/-- `ParseError::is_no_leading_backslash` part of `JsonptrDerivedProofs.parseErrorAccessors`. -/
theorem parseErrorIsNoLeadingBackslash (e : pointer.ParseError) :
    pointer.ParseError.is_no_leading_backslash e = .ok (peIsNls e) :=
  (JsonptrDerivedProofs.parseErrorAccessors e).2.2.2.2.1

/-- `ParseError::is_invalid_encoding` part of `JsonptrDerivedProofs.parseErrorAccessors`. -/
theorem parseErrorIsInvalidEncoding (e : pointer.ParseError) :
    pointer.ParseError.is_invalid_encoding e = .ok (!peIsNls e) :=
  (JsonptrDerivedProofs.parseErrorAccessors e).2.2.2.2.2

end JsonptrPublication
