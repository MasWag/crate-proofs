import Statements.DefaultDerived

/-! # Proofs for the release-extractable items (implementation agent) -/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrDerivedSpec jsonptr

namespace JsonptrDerivedProofs

theorem ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = .ok x ∧ P x := by
  cases hm : m with
  | ret out => exact ⟨out, rfl, (spec_ok out).mp (hm ▸ h)⟩
  | div => exact False.elim (spec_div.mp (hm ▸ h))
  | vis e k => exact False.elim ((spec_vis e k).mp (hm ▸ h))

theorem indexClone : IndexCloneContract := fun _ => rfl
theorem indexFrom : IndexFromContract := fun _ => rfl
theorem asStr : AsStrContract := fun _ => rfl

theorem indexEq : IndexEqContract := by
  intro a b
  cases a <;> cases b <;> simp [index.Index.Insts.CoreCmpPartialEqIndex.eq, index.Index.read_discriminant, lift]

theorem parseErrorAccessors : ParseErrorAccessorsContract := by
  intro e; cases e <;> simp [pointer.ParseError.offset, pointer.ParseError.pointer_offset,
    pointer.ParseError.source_offset, pointer.ParseError.is_no_leading_slash,
    pointer.ParseError.is_no_leading_backslash, pointer.ParseError.is_invalid_encoding, peOff, peSrc, peIsNls]

theorem completeOffset : CompleteOffsetContract := by
  intro e h
  cases e with
  | NoLeadingSlash =>
    obtain ⟨n, hn, hv⟩ := ok_of_spec (Usize.add_spec (x := 0#usize) (y := 0#usize) (by simp))
    refine ⟨n, ?_, by simp only [peOff, peSrc]; scalar_tac⟩
    unfold pointer.ParseError.complete_offset pointer.ParseError.source_offset pointer.ParseError.pointer_offset
    simpa using hn
  | InvalidEncoding d s =>
    simp only [peOff, peSrc] at h ⊢
    obtain ⟨n, hn, hv⟩ := ok_of_spec (Usize.add_spec (x := s.offset) (y := d) (by omega))
    exact ⟨n, by simp [pointer.ParseError.complete_offset, pointer.ParseError.source_offset,
      pointer.ParseError.pointer_offset, hn], by scalar_tac⟩

theorem usize_max_add_one : (core.num.Usize.MAX + 1#usize : Result Usize) = .fail .integerOverflow := by
  have hv : core.num.Usize.MAX.val = Usize.max := by simp [core.num.Usize.MAX]
  show UScalar.add core.num.Usize.MAX 1#usize = _
  simp only [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, Result.ofOption]
  rw [dif_neg]
  simp only [UScalar.check_bounds, decide_eq_true_eq, not_lt]
  rw [hv, Usize.max_def]
  have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
  simp [Usize.numBits] at *

/-- N7, checked: `complete_offset` overflows on the publicly constructible
error `InvalidEncoding { offset: usize::MAX, source: { offset: 1, .. } }`. -/
theorem completeOffsetTotal_refuted : ¬ CompleteOffsetTotalContract := by
  intro h
  obtain ⟨n, hn⟩ := h (.InvalidEncoding 1#usize ⟨core.num.Usize.MAX, .Tilde⟩)
  have : (core.num.Usize.MAX + 1#usize : Result Usize) = .ok n := by
    simpa [pointer.ParseError.complete_offset, pointer.ParseError.source_offset,
      pointer.ParseError.pointer_offset] using hn
  rw [usize_max_add_one] at this; exact absurd this (by simp)

theorem str_ne_of_len {a b : Str} (h : a.val.length ≠ b.val.length) : a ≠ b := fun e => h (by rw [e])

theorem encodingErrorUrl : EncodingErrorUrlContract := rfl
theorem assignErrorUrl : AssignErrorUrlContract := rfl

/-- N3, checked: `resolve::Error::url` returns the `assign::Error` address. -/
theorem resolveErrorUrl_refuted : ¬ ResolveErrorUrlContract := by
  intro h
  simp only [ResolveErrorUrlContract, resolve.Error.Insts.JsonptrDiagnosticDiagnosticPointerBufPointer.url,
    Result.ok.injEq] at h
  have := congrArg (fun s : Str => s.val.length) h
  simp [toStr, ByteArray.length_toList] at this
  exact absurd this (by decide)

/-- N10, checked: `ParseError::url` names a struct page for an enum. -/
theorem parseErrorUrl_refuted : ¬ ParseErrorUrlContract := by
  intro h
  simp only [ParseErrorUrlContract, pointer.ParseError.Insts.JsonptrDiagnosticDiagnosticStringStr.url,
    Result.ok.injEq] at h
  have := congrArg (fun s : Str => s.val.length) h
  simp [toStr, ByteArray.length_toList] at this
  exact absurd this (by decide)

/-- N9, checked: `ParseIndexError::url` omits the `index` module. -/
theorem parseIndexErrorUrl_refuted : ¬ ParseIndexErrorUrlContract := by
  intro h
  simp only [ParseIndexErrorUrlContract, index.ParseIndexError.Insts.JsonptrDiagnosticDiagnosticStringOrTokenStr.url,
    Result.ok.injEq] at h
  have := congrArg (fun s : Str => s.val.length) h
  simp [toStr, ByteArray.length_toList] at this
  exact absurd this (by decide)

/-- Behaviour record for the three `url`s that match the intended address, and
for `resolve::Error`, the address the release returns. -/
theorem url_record :
    pointer.ParseError.Insts.JsonptrDiagnosticDiagnosticStringStr.url =
      .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/struct.ParseError.html") ∧
    token.EncodingError.Insts.JsonptrDiagnosticDiagnosticStringStr.url =
      .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/struct.EncodingError.html") ∧
    assign.Error.Insts.JsonptrDiagnosticDiagnosticPointerBufPointer.url =
      .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/assign/enum.Error.html") ∧
    resolve.Error.Insts.JsonptrDiagnosticDiagnosticPointerBufPointer.url =
      .ok (toStr "https://docs.rs/jsonptr/0.8.2/jsonptr/assign/enum.Error.html") :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem urlRecord : ParseIndexErrorUrlRecord := rfl

theorem labelNew : LabelNewContract := fun t o l => ⟨_, rfl, rfl, rfl, rfl⟩

theorem reportAccessors : ReportAccessorsContract := fun _ => ⟨rfl, rfl, rfl⟩

theorem invalidEncoding : InvalidEncodingContract := by
  intro a b
  refine ⟨by cases a <;> rfl, ?_⟩
  cases a <;> cases b <;> simp [token.InvalidEncoding.Insts.CoreCmpPartialEqInvalidEncoding.eq,
    token.InvalidEncoding.read_discriminant]

theorem oobEqClone : OobEqCloneContract := by
  rintro ⟨l, i⟩ ⟨l', i'⟩
  refine ⟨by simp [index.OutOfBoundsError.Insts.CoreCloneClone.clone, lift], ?_⟩
  by_cases h1 : l = l' <;> by_cases h2 : i = i' <;>
    simp [index.OutOfBoundsError.Insts.CoreCmpPartialEqOutOfBoundsError.eq, h1, h2, lift]

theorem ice : IceContract := by
  rintro ⟨o⟩ ⟨o'⟩
  refine ⟨by simp [index.InvalidCharacterError.Insts.CoreCloneClone.clone, lift], rfl, ?_⟩
  by_cases h : o = o' <;>
    simp [index.InvalidCharacterError.Insts.CoreCmpPartialEqInvalidCharacterError.eq, h, lift]

theorem encodingErrorEq : EncodingErrorEqContract := by
  rintro ⟨o, s⟩ ⟨o', s'⟩
  by_cases h : o = o' <;> cases s <;> cases s' <;>
    simp [token.EncodingError.Insts.CoreCmpPartialEqEncodingError.eq,
      token.InvalidEncoding.Insts.CoreCmpPartialEqInvalidEncoding.eq,
      token.InvalidEncoding.read_discriminant, h, lift]

theorem replaceErrorEq : ReplaceErrorEqContract := by
  rintro ⟨i, c⟩ ⟨i', c'⟩
  by_cases h1 : i = i' <;> by_cases h2 : c = c' <;>
    simp [pointer.ReplaceError.Insts.CoreCmpPartialEqReplaceError.eq, h1, h2, lift]

theorem parseErrorEq : ParseErrorEqContract := by
  intro a b
  cases a with
  | NoLeadingSlash =>
    cases b <;> simp [pointer.ParseError.Insts.CoreCmpPartialEqParseError.eq, pointer.ParseError.read_discriminant]
  | InvalidEncoding d e =>
    cases b with
    | NoLeadingSlash => simp [pointer.ParseError.Insts.CoreCmpPartialEqParseError.eq, pointer.ParseError.read_discriminant]
    | InvalidEncoding d' e' =>
      obtain ⟨r, hr, hm⟩ := encodingErrorEq e e'
      by_cases h : d = d'
      · refine ⟨r, by simp [pointer.ParseError.Insts.CoreCmpPartialEqParseError.eq,
          pointer.ParseError.read_discriminant, h, lift, hr], ?_⟩
        rw [hm]; simp [h]
      · exact ⟨false, by simp [pointer.ParseError.Insts.CoreCmpPartialEqParseError.eq,
          pointer.ParseError.read_discriminant, h, lift], by simp [h]⟩

theorem indexCmp : IndexCmpContract := by
  intro a b
  have hc : index.Index.Insts.CoreCmpOrd.cmp a b = .ok (indexOrd a b) := by
    cases a <;> cases b <;> simp [index.Index.Insts.CoreCmpOrd.cmp, index.Index.read_discriminant, lift, indexOrd] <;> rfl
  refine ⟨hc, ?_⟩
  simp [index.Index.Insts.CoreCmpPartialOrdIndex.partial_cmp, hc]

end JsonptrDerivedProofs
