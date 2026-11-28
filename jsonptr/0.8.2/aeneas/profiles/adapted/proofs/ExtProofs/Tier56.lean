import Statements.Tier5Err
import Statements.Tier6Acc
import ExtProofs.Tier3

/-! # Tier 5/6 proofs and refutations (subset), implementation agent -/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem isRootAdapted : IsRootContract := by
  intro xs _
  refine ⟨_, rfl, ?_⟩
  simp [jsonptr.adapted_api.is_root_adapted, bytes]

theorem lenAdapted : LenContract := fun xs _ => ⟨_, rfl, by simp⟩

theorem strEqAdapted : StrEqContract := by
  intro a b
  obtain ⟨r, hr, hm⟩ := ok_of_spec (bytesEq_spec a b)
  exact ⟨r, by simp [jsonptr.adapted_api.str_eq_adapted, hr], hm⟩

theorem componentEqAdapted : ComponentEqContract := by
  intro a b
  cases a with
  | Root => cases b <;> simp [jsonptr.adapted_api.component_eq_adapted, component]
  | Token x =>
    cases b with
    | Root => simp [jsonptr.adapted_api.component_eq_adapted, component]
    | Token y =>
      obtain ⟨r, hr, hm⟩ := strEqAdapted x y
      exact ⟨r, by simp [jsonptr.adapted_api.component_eq_adapted, hr], by simp [component, hm]⟩

theorem bufCloneAdapted : BufCloneContract := by
  intro buf
  obtain ⟨s', hs, heq⟩ := ok_of_spec (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := buf.slice)
    (fun x _ => rfl))
  refine ⟨{ slice := s' }, by simp [jsonptr.adapted_api.buf_clone_adapted, alloc.vec.CloneVec.clone, hs], ?_⟩
  rw [← heq]

theorem resolveErrorAccessors : ResolveErrorAccessorsContract := by
  intro e; cases e <;> simp [jsonptr.adapted_api.resolve_err.resolve_error_offset_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_position_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_is_unreachable_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_is_not_found_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_is_out_of_bounds_adapted,
    jsonptr.adapted_api.resolve_err.resolve_error_is_failed_to_parse_index_adapted,
    resolveErrFields, resolveErrVariant]

/-! ## Checked refutations (JSONPTR-003, N5, N8) -/

theorem usize_zero_sub_one : (0#usize - 1#usize : Result Usize) = .fail .integerOverflow := by
  show UScalar.sub 0#usize 1#usize = _
  simp [UScalar.sub]

theorem emptySlice_len : emptySlice.len = 0#usize := by
  apply UScalar.eq_of_val_eq; simp [emptySlice]

def slTilde : Slice U8 := Slice.from [47#u8, 126#u8] (by simp; scalar_tac)

/-- JSONPTR-003, checked: for the subject `"/~"` the parser's error is
`InvalidEncoding { offset: 0, source: { offset: 1, Tilde } }`; the release
length is 2, the intended length is 1. -/
theorem invalidEncodingLen_refuted : ¬ InvalidEncodingLenContract := by
  intro h
  have hb : bytes slTilde = [47, 126] := by simp [bytes, slTilde]
  have hpe : pointerError (bytes slTilde) = some (.invalidEncoding 0 1) := by rw [hb]; decide
  obtain ⟨n, hn, hv⟩ := h (.InvalidEncoding 0#usize ⟨1#usize, .Tilde⟩) slTilde _ hpe (by simp [ptrOutcome])
  have hlen : slTilde.len = 2#usize := by apply UScalar.eq_of_val_eq; simp [slTilde]
  obtain ⟨d, hd, hdv⟩ := ok_of_spec (Usize.sub_spec (x := 2#usize) (y := 1#usize) (by simp))
  have hdv' : d.val = 1 := by simpa using hdv
  simp [jsonptr.adapted_api.invalid_encoding_len_adapted, hlen, hd, hdv'] at hn
  rw [hb] at hv; simp [invalidEncodingLen] at hv
  rw [← hn] at hv; simp at hv

/-- N8, checked: `EncodingError { offset: 0, Tilde }` on the empty subject
underflows (`offset - 1`). -/
theorem encodingErrorLabelTotal_refuted : ¬ EncodingErrorLabelTotalContract := by
  intro h
  obtain ⟨sp, hsp⟩ := h ⟨0#usize, .Tilde⟩ emptySlice
  simp [jsonptr.adapted_api.encoding_error_label_adapted, emptySlice_len, usize_zero_sub_one] at hsp

/-- N5, checked: `invalid_encoding_len` on the empty subject underflows
(`subject.len() - 1`). -/
theorem invalidEncodingLenTotal_refuted : ¬ InvalidEncodingLenTotalContract := by
  intro h
  obtain ⟨n, hn⟩ := h (.InvalidEncoding 0#usize ⟨1#usize, .Tilde⟩) emptySlice
  simp [jsonptr.adapted_api.invalid_encoding_len_adapted, emptySlice_len, usize_zero_sub_one] at hn

end JsonptrExtProofs
