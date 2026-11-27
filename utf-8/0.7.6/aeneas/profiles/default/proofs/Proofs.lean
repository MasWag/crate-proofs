import Utf8

open Aeneas Aeneas.Std Result
open Aeneas.Std.WP

namespace Utf8Proofs

private theorem total_of_spec {α} (m : Result α) (p : α → Prop)
    (h : spec m p) : ∃ out, m = .ok out ∧ p out := by
  induction m using Result.cases with
  | ret x => exact ⟨x, rfl, (spec_ok x).mp h⟩
  | vis e k => simp only [spec_vis] at h
  | div => simp only [spec_div] at h


theorem empty_total :
    ∃ state, utf8.Incomplete.empty = .ok state ∧
      state.buffer.val = List.replicate 4 (0#u8) ∧ state.buffer_len.val = 0 := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem is_empty_total (state : utf8.Incomplete) :
    ∃ empty, state.is_empty = .ok empty ∧ (empty = true ↔ state.buffer_len.val = 0) := by
  refine ⟨_, rfl, ?_⟩
  simp
  scalar_tac

theorem new_total (bytes : Slice U8) (bounded : bytes.val.length ≤ 4) :
    ∃ state, utf8.Incomplete.new bytes = .ok state ∧
      state.buffer.val = bytes.val ++ List.replicate (4 - bytes.val.length) (0#u8) ∧
      state.buffer_len.val = bytes.val.length := by
  have lenBound : bytes.len ≤ 4#usize := by scalar_tac
  have castBound : bytes.len.val ≤ UScalar.max .U8 := by scalar_tac
  apply total_of_spec
  unfold utf8.Incomplete.new
  step as ⟨segment, back, hSegment, hLength, hBack⟩
  step as ⟨copied, hCopy⟩
  step with UScalar.cast_inBounds_spec .U8 bytes.len castBound as ⟨size, hSize⟩
  constructor
  · rw [hBack, hCopy, Array.repeat_val]
    have four : (4#usize).val = 4 := rfl
    simp only [List.setSlice!, List.length_replicate, four, Nat.sub_zero, Nat.zero_add, Nat.min_eq_left bounded, List.take_length, List.take_zero, List.nil_append, List.drop_replicate]
  · simpa using hSize

theorem take_buffer_total (state : utf8.Incomplete) (bounded : state.buffer_len.val ≤ 4) :
    ∃ result, state.take_buffer = .ok result ∧
      result.1.val = state.buffer.val.take state.buffer_len.val ∧
      result.2.buffer.val = state.buffer.val ∧ result.2.buffer_len.val = 0 := by
  have castBound : state.buffer_len.val ≤ UScalar.max .Usize := by scalar_tac
  apply total_of_spec
  unfold utf8.Incomplete.take_buffer
  step with UScalar.cast_inBounds_spec .Usize state.buffer_len castBound as ⟨size, hSize⟩
  step as ⟨segment, hPrefix⟩
  simp only [List.slice, List.drop_zero, Nat.sub_zero] at *
  exact ⟨by simpa [hSize] using hPrefix, rfl⟩

theorem incomplete_clone_total (state : utf8.Incomplete) :
    ∃ out, utf8.Incomplete.Insts.CoreCloneClone.clone state = .ok out ∧ out = state := by
  exact ⟨state, rfl, rfl⟩

theorem decode_error_clone_total (error : utf8.DecodeError) :
    ∃ out, utf8.DecodeError.Insts.CoreCloneClone.clone error = .ok out ∧ out = error := by
  exact ⟨error, rfl, rfl⟩

theorem lossy_new_total {F : Type} (callback : F) :
    ∃ out, utf8.lossy.LossyDecoder.new callback = .ok out ∧
      out.push_str = callback ∧ out.incomplete.buffer.val = List.replicate 4 (0#u8) ∧
      out.incomplete.buffer_len.val = 0 := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem bufread_new_total {B : Type} (reader : B) :
    ∃ out, utf8.read.BufReadDecoder.new reader = .ok out ∧
      out.buf_read = reader ∧ out.bytes_consumed.val = 0 ∧
      out.incomplete.buffer.val = List.replicate 4 (0#u8) ∧ out.incomplete.buffer_len.val = 0 := by
  refine ⟨{buf_read := reader, bytes_consumed := (0#usize), incomplete := {buffer := Array.repeat 4#usize 0#u8, buffer_len := 0#u8}}, ?_, rfl, rfl, rfl, rfl⟩
  simp [utf8.read.BufReadDecoder.new, utf8.Incomplete.empty]

end Utf8Proofs
