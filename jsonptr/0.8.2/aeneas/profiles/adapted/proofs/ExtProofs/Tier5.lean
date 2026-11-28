import ExtProofs.Tier56
import Proofs

/-! # Tier 5 labels, accessors, diagnose (implementation agent) -/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem isCont_eq (b : U8) : jsonptr.adapted_api.is_cont_adapted b = .ok (decide (128 ≤ b.val ∧ b.val ≤ 191)) := by
  unfold jsonptr.adapted_api.is_cont_adapted
  split
  · by_cases h : b.val ≤ 191
    · have : b ≤ 191#u8 := by scalar_tac
      simp [this, h]; scalar_tac
    · have : ¬ b ≤ 191#u8 := by scalar_tac
      simp [this, h]
  · have : ¬ 128 ≤ b.val := by scalar_tac
    simp [this]

/-- Weak spec: a result is found only at a non-`'0'` byte. -/
theorem posNonZero_spec (s : Slice U8) :
    jsonptr.adapted_api.position_non_zero_char_adapted s ⦃ o =>
      o = none ∨ ∃ (k : Nat) (b : U8), s.val[k]? = some b ∧ b.val ≠ 48 ⦄ := by
  unfold jsonptr.adapted_api.position_non_zero_char_adapted jsonptr.adapted_api.position_non_zero_char_adapted_loop
  apply loop.spec_decr_nat (fun p : Usize × Usize => s.length - p.1.val)
    (fun p => p.1.val ≤ s.length ∧ p.2.val ≤ p.1.val)
  · rintro ⟨i, c⟩ ⟨h1, h2⟩
    simp only at h1 h2
    simp only [jsonptr.adapted_api.position_non_zero_char_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi); intro x hx
      rw [isCont_eq]; apply spec_bind_ok
      split
      next => step as ⟨i4, hi4⟩; refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
      next =>
        split
        next hne =>
          apply (spec_ok _).mpr; right
          refine ⟨i.val, x, by rw [List.getElem?_eq_getElem hi, hx], ?_⟩
          have hne' : x ≠ 48#u8 := by simpa using hne
          intro e; exact hne' (UScalar.eq_of_val_eq (by simpa using e))
        next =>
          step as ⟨i4, hi4⟩; step as ⟨i5, hi5⟩
          refine ⟨by scalar_tac, by scalar_tac, by scalar_tac⟩
    next => exact (spec_ok _).mpr (Or.inl rfl)
  · exact ⟨by simp, by simp⟩

/-- Weak spec: a digit is reported only at a byte index at least `skip`. -/
theorem posDigitAfter_spec (s : Slice U8) (skip : Usize) :
    jsonptr.adapted_api.position_digit_after_chars_adapted s skip ⦃ o =>
      o = none ∨ ∃ (k : Nat) (b : U8), skip.val ≤ k ∧ s.val[k]? = some b ∧ isDigit b.val = true ⦄ := by
  unfold jsonptr.adapted_api.position_digit_after_chars_adapted jsonptr.adapted_api.position_digit_after_chars_adapted_loop
  apply loop.spec_decr_nat (fun p : Usize × Usize × Usize => s.length - p.1.val)
    (fun p => p.1.val ≤ s.length ∧ p.2.1.val ≤ p.1.val ∧ p.2.2.val ≤ p.1.val)
  · rintro ⟨i, c, q⟩ ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    simp only [jsonptr.adapted_api.position_digit_after_chars_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi); intro x hx
      rw [isCont_eq]; apply spec_bind_ok
      split
      next => step as ⟨i5, hi5⟩; refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
      next =>
        split
        next hge =>
          rw [JsonptrAdaptedProofs.isAsciiDigit_eq]; apply spec_bind_ok
          split
          next hd =>
            apply (spec_ok _).mpr; right
            exact ⟨i.val, x, by scalar_tac, by rw [List.getElem?_eq_getElem hi, hx], hd⟩
          next =>
            step as ⟨a, ha⟩; step as ⟨b, hb⟩; step as ⟨d, hd⟩
            refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
        next =>
          step as ⟨a, ha⟩; step as ⟨b, hb⟩
          refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac⟩
    next => exact (spec_ok _).mpr (Or.inl rfl)
  · exact ⟨by simp, by simp, by simp⟩

def s00 : Slice U8 := Slice.from [48#u8, 48#u8] (by simp; scalar_tac)
def s1abc : Slice U8 := Slice.from [49#u8, 97#u8, 98#u8, 99#u8] (by simp; scalar_tac)

/-- N1, checked: on `"00"` (`LeadingZeros`) the release `expect` panics. -/
theorem parseIndexErrorLabel_N1 :
    ∃ e, jsonptr.adapted_api.parse_index_error_label_adapted .LeadingZeros s00 = .fail e := by
  obtain ⟨o, ho, hpost⟩ := ok_of_spec (posNonZero_spec s00)
  rcases hpost with rfl | ⟨k, b, hk, hb⟩
  · exact ⟨.panic, by simp [jsonptr.adapted_api.parse_index_error_label_adapted, ho]⟩
  · exfalso
    simp [s00] at hk
    rcases k with _ | _ | k <;> simp at hk <;> (subst hk; simp at hb)

/-- N2, checked: on `"1abc"` (`InvalidCharacter` at 1) the release length is 4,
the whole subject, where the intended run of non-digits is 3. -/
theorem parseIndexErrorLabel_N2 :
    jsonptr.adapted_api.parse_index_error_label_adapted (.InvalidCharacter ⟨1#usize⟩) s1abc =
      .ok (some ⟨1#usize, 4#usize⟩) := by
  obtain ⟨o, ho, hpost⟩ := ok_of_spec (posDigitAfter_spec s1abc 1#usize)
  rcases hpost with rfl | ⟨k, b, hk1, hk, hb⟩
  · have hl : s1abc.len = 4#usize := by apply UScalar.eq_of_val_eq; simp [s1abc]
    simp only [jsonptr.adapted_api.parse_index_error_label_adapted]
    rw [ho]; simp [hl]
  · exfalso
    simp [s1abc] at hk
    rcases k with _ | _ | _ | _ | k <;> simp at hk hk1 <;> (subst hk; simp [isDigit] at hb)

theorem parseIndexErrorLabel_refuted : ¬ ParseIndexErrorLabelContract := by
  intro h
  have hb : bytes s00 = [48, 48] := by simp [bytes, s00]
  obtain ⟨o, ho, _⟩ := h .LeadingZeros s00 (by rw [hb]; decide)
  obtain ⟨e, he⟩ := parseIndexErrorLabel_N1
  rw [ho] at he; simp at he

theorem parseIndexErrorLabel_refuted_N2 : ¬ ParseIndexErrorLabelContract := by
  intro h
  have hb : bytes s1abc = [49, 97, 98, 99] := by simp [bytes, s1abc]
  obtain ⟨o, ho, hpost⟩ := h (.InvalidCharacter ⟨1#usize⟩) s1abc (by rw [hb]; decide)
  rw [parseIndexErrorLabel_N2] at ho
  simp only [Result.ok.injEq] at ho; subst ho
  simp [ospan, IndexErrLabelPost, indexError, hb, countWhile, isDigit] at hpost

/-! ## Token-error labels -/

theorem resolveErrPos (e : jsonptr.resolve.ResolveErrorAdapted) :
    jsonptr.adapted_api.resolve_err.resolve_error_position_adapted e = .ok (resolveErrFields e).1 ∧
    jsonptr.adapted_api.resolve_err.resolve_error_offset_adapted e = .ok (resolveErrFields e).2 :=
  ⟨(resolveErrorAccessors e).2.1, (resolveErrorAccessors e).1⟩

theorem assignErrorAccessors : AssignErrorAccessorsContract := by
  intro e; cases e <;> simp [jsonptr.adapted_api.doc_mut.assign_error_position_adapted,
    jsonptr.adapted_api.doc_mut.assign_error_offset_adapted,
    jsonptr.adapted_api.doc_mut.assign_error_is_out_of_bounds_adapted,
    jsonptr.adapted_api.doc_mut.assign_error_is_failed_to_parse_index_adapted, assignErrFields]

/-- The shared tail of both token-error label bodies. -/
theorem tokenLabel_tail (origin : Slice U8) (off : Usize) (t : Slice U8) (hoff : off.val < Usize.max) :
    (do
      let i2 ← off + 1#usize
      let i4 ← if i2 < Slice.len origin then off + 1#usize else Result.ok off
      Result.ok (some ({ offset := i4, len := Slice.len t } : jsonptr.adapted_api.SpanAdapted))) ⦃ o =>
      ospan o = some ⟨if off.val + 1 < (bytes origin).length then off.val + 1 else off.val, (bytes t).length⟩ ⦄ := by
  step as ⟨i2, hi2⟩
  split
  next hlt =>
    step as ⟨i4, hi4⟩
    have : off.val + 1 < (bytes origin).length := by simp; scalar_tac
    simp only [bytes_length] at this
    simp [ospan, this, hi4]
  next hge =>
    have : ¬ off.val + 1 < (bytes origin).length := by simp; scalar_tac
    simp only [bytes_length] at this
    apply spec_bind_ok
    apply (spec_ok _).mpr
    simp [ospan, this]

theorem resolveErrorLabelAdapted : ResolveErrorLabelContract := by
  intro e origin hv hoff
  obtain ⟨hp, ho⟩ := resolveErrPos e
  obtain ⟨r, hr, hm, _⟩ := getIndexAdapted origin (resolveErrFields e).1 hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.resolve_err.resolve_error_label_adapted
  rw [hp]; apply spec_bind_ok
  rw [hr]; apply spec_bind_ok
  cases r with
  | none =>
    apply (spec_ok _).mpr
    simp [ospan, tokenErrLabel, ← hm, obytes]
  | some t =>
    rw [ho]; apply spec_bind_ok
    apply spec_mono (tokenLabel_tail origin _ t hoff)
    intro o h
    rw [h]; simp [tokenErrLabel, ← hm, obytes]

theorem resolveErrorLabelTotal_refuted : ¬ ResolveErrorLabelTotalContract := by
  intro h
  have hvA : ValidPtr slA := by
    rw [ValidPtr, slA_bytes]; apply valid_47; simp [noBad_cons, noBad_nil]
  obtain ⟨o, ho⟩ := h (.NotFound 0#usize core.num.Usize.MAX) slA hvA
  obtain ⟨r, hr, hm, _⟩ := getIndexAdapted slA 0#usize hvA
  have hsome : ∃ t, r = some t := by
    cases r with
    | some t => exact ⟨t, rfl⟩
    | none => simp [obytes, getToken, slA_bytes, encodedTokens, splitSlash] at hm
  obtain ⟨t, rfl⟩ := hsome
  simp [jsonptr.adapted_api.resolve_err.resolve_error_label_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_position_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_offset_adapted, hr, usize_max_add_one] at ho

theorem assignErrorLabelAdapted : AssignErrorLabelContract := by
  intro e origin hv hoff
  obtain ⟨hp, ho, _, _⟩ := assignErrorAccessors e
  obtain ⟨r, hr, hm, _⟩ := getIndexAdapted origin (assignErrFields e).1 hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.doc_mut.assign_error_label_adapted
  rw [hp]; apply spec_bind_ok
  rw [hr]; apply spec_bind_ok
  cases r with
  | none =>
    apply (spec_ok _).mpr
    simp [ospan, tokenErrLabel, ← hm, obytes]
  | some t =>
    rw [ho]; apply spec_bind_ok
    apply spec_mono (tokenLabel_tail origin _ t hoff)
    intro o h
    rw [h]; simp [tokenErrLabel, ← hm, obytes]

theorem assignErrorLabelTotal_refuted : ¬ AssignErrorLabelTotalContract := by
  intro h
  have hvA : ValidPtr slA := by
    rw [ValidPtr, slA_bytes]; apply valid_47; simp [noBad_cons, noBad_nil]
  obtain ⟨o, ho⟩ := h (.OutOfBounds 0#usize core.num.Usize.MAX ⟨0#usize, 0#usize⟩) slA hvA
  obtain ⟨r, hr, hm, _⟩ := getIndexAdapted slA 0#usize hvA
  have hsome : ∃ t, r = some t := by
    cases r with
    | some t => exact ⟨t, rfl⟩
    | none => simp [obytes, getToken, slA_bytes, encodedTokens, splitSlash] at hm
  obtain ⟨t, rfl⟩ := hsome
  simp [jsonptr.adapted_api.doc_mut.assign_error_label_adapted,
    jsonptr.adapted_api.doc_mut.assign_error_position_adapted,
    jsonptr.adapted_api.doc_mut.assign_error_offset_adapted, hr, usize_max_add_one] at ho

theorem diagnoseAdapted : DiagnoseContract := by
  intro r s; cases r <;> simp [jsonptr.adapted_api.diagnose_parse_adapted]

/-- JSONPTR-003 for `ParseError::labels`, checked. -/
theorem parseErrorLabel_refuted : ¬ ParseErrorLabelContract := by
  intro h
  have hb : bytes slTilde = [47, 126] := by simp [bytes, slTilde]
  have hpe : pointerError (bytes slTilde) = some (.invalidEncoding 0 1) := by rw [hb]; decide
  obtain ⟨sp, hsp, hv⟩ := h (.InvalidEncoding 0#usize ⟨1#usize, .Tilde⟩) slTilde _ hpe (by simp [ptrOutcome])
  have hlen : slTilde.len = 2#usize := by apply UScalar.eq_of_val_eq; simp [slTilde]
  obtain ⟨d, hd, hdv⟩ := ok_of_spec (Usize.sub_spec (x := 2#usize) (y := 1#usize) (by simp))
  have hdv' : d.val = 1 := by simpa using hdv
  obtain ⟨c, hc, _⟩ := ok_of_spec (Usize.add_spec (x := 1#usize) (y := 0#usize) (by scalar_tac))
  simp [jsonptr.adapted_api.parse_error_label_adapted, jsonptr.pointer.ParseError.complete_offset,
    jsonptr.pointer.ParseError.source_offset, jsonptr.pointer.ParseError.pointer_offset, hc,
    jsonptr.adapted_api.invalid_encoding_len_adapted, hlen, hd, hdv'] at hsp
  rw [hb] at hv; simp [ptrErrLabel, invalidEncodingLen] at hv
  rw [← hsp] at hv; simp at hv

end JsonptrExtProofs
