import CoreAdapted
open Aeneas Aeneas.Std Result ControlFlow Error
namespace unindent.Proofs
set_option maxHeartbeats 2000000
/-- A line scanner terminates at the first LF or the end of the slice. -/
theorem line_end_spec (s : Slice U8) (start : Usize) (hstart : start.val ≤ s.val.length) :
    WP.spec (line_end_index s start) (fun out =>
      start.val ≤ out.val ∧ out.val ≤ s.val.length ∧
      (out.val = s.val.length ∨ s.val[out.val]? = some 10#u8) ∧
      ∀ j, start.val ≤ j → j < out.val → s.val[j]? ≠ some 10#u8) := by
  unfold line_end_index line_end_index_loop
  apply loop.spec_decr_nat
    (measure := fun i : Usize => s.val.length - i.val)
    (inv := fun i : Usize => start.val ≤ i.val ∧ i.val ≤ s.val.length ∧
      ∀ j, start.val ≤ j → j < i.val → s.val[j]? ≠ some 10#u8)
  · intro i hi
    obtain ⟨hsi, hil, hprefix⟩ := hi
    unfold line_end_index_loop.body
    by_cases hlt : i.val < s.val.length
    · have hmax := Slice.length_ineq s
      have hadd : i.val + 1 ≤ Usize.max := by omega
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte]
      apply WP.spec_bind (Slice.index_usize_spec s i hlt)
      intro b hb
      split <;> rename_i hbyte
      · apply WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro j hj
        have hj' : j.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        intro k hsk hkj
        by_cases hki : k < i.val
        · exact hprefix k hsk hki
        · have heq : k = i.val := by omega
          subst k
          simp_all
      · simp only [WP.spec_ok]
        refine ⟨hsi, hil, Or.inr ?_, hprefix⟩
        have heq : b = 10#u8 := by scalar_tac
        simpa only [List.getElem?_eq_getElem hlt] using congrArg some (hb.symm.trans heq)
    · have hmax := Slice.length_ineq s
      simp only [UScalar.lt_equiv, Slice.len_val, hlt, ↓reduceIte, WP.spec_ok]
      exact ⟨hsi, hil, Or.inl (by omega), hprefix⟩
  · exact ⟨Nat.le_refl _, hstart, by omega⟩
/-- The margin scanner returns the first byte other than SPACE/TAB, or the line end. -/
theorem leading_end_spec (s : Slice U8) (start finish : Usize)
    (hs : start.val ≤ finish.val) (hf : finish.val ≤ s.val.length) :
    WP.spec (leading_end_index s start finish) (fun out =>
      start.val ≤ out.val ∧ out.val ≤ finish.val ∧
      (out.val = finish.val ∨ (s.val[out.val]? ≠ some 32#u8 ∧
        s.val[out.val]? ≠ some 9#u8)) ∧
      ∀ j, start.val ≤ j → j < out.val →
        s.val[j]? = some 32#u8 ∨ s.val[j]? = some 9#u8) := by
  unfold leading_end_index leading_end_index_loop
  apply loop.spec_decr_nat
    (measure := fun i : Usize => finish.val - i.val)
    (inv := fun i : Usize => start.val ≤ i.val ∧ i.val ≤ finish.val ∧
      ∀ j, start.val ≤ j → j < i.val →
        s.val[j]? = some 32#u8 ∨ s.val[j]? = some 9#u8)
  · intro i hi
    obtain ⟨hsi, hif, hp⟩ := hi
    unfold leading_end_index_loop.body
    by_cases hlt : i.val < finish.val
    · simp only [UScalar.lt_equiv, hlt, ↓reduceIte]
      have hil : i.val < s.val.length := by omega
      apply WP.spec_bind (Slice.index_usize_spec s i hil)
      intro b hb
      split <;> rename_i hb32
      · apply WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
        intro k hk
        have hk' : k.val = i.val + 1 := by scalar_tac
        simp only [WP.spec_ok]
        refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
        intro j hsj hjk
        by_cases hji : j < i.val
        · exact hp j hsj hji
        · have hji : j = i.val := by omega
          subst j
          left
          simpa only [List.getElem?_eq_getElem hil] using congrArg some (hb.symm.trans hb32)
      · split <;> rename_i hb9
        · apply WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
          intro k hk
          have hk' : k.val = i.val + 1 := by scalar_tac
          simp only [WP.spec_ok]
          refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
          intro j hsj hjk
          by_cases hji : j < i.val
          · exact hp j hsj hji
          · have hji : j = i.val := by omega
            subst j
            right
            simpa only [List.getElem?_eq_getElem hil] using congrArg some (hb.symm.trans hb9)
        · simp only [WP.spec_ok]
          refine ⟨hsi, hif, Or.inr ?_, hp⟩
          constructor
          · intro he
            have heq : s.val[i.val] = 32#u8 := Option.some.inj
              (by simpa only [List.getElem?_eq_getElem hil] using he)
            exact hb32 (hb.trans heq)
          · intro he
            have heq : s.val[i.val] = 9#u8 := Option.some.inj
              (by simpa only [List.getElem?_eq_getElem hil] using he)
            exact hb9 (hb.trans heq)
    · simp only [UScalar.lt_equiv, hlt, ↓reduceIte, WP.spec_ok]
      exact ⟨hsi, hif, Or.inl (by omega), hp⟩
  · exact ⟨Nat.le_refl _, hs, by omega⟩
end unindent.Proofs
unseal Aeneas.Std.Result in
theorem unindent.Proofs.line_end_total_exact (s : Aeneas.Std.Slice Aeneas.Std.U8)
    (start : Aeneas.Std.Usize) (hstart : start.val ≤ s.val.length) :
    ∃ out, unindent.line_end_index s start = Aeneas.Std.Result.ok out ∧
      start.val ≤ out.val ∧ out.val ≤ s.val.length ∧
      (out.val = s.val.length ∨ s.val[out.val]? = some 10#u8) ∧
      ∀ j, start.val ≤ j → j < out.val → s.val[j]? ≠ some 10#u8 := by
  have h := unindent.Proofs.line_end_spec s start hstart
  generalize he : unindent.line_end_index s start = m at h ⊢
  cases m using Aeneas.Data.Coinductive.ITree.cases with
  | ret out => exact ⟨out, rfl, Aeneas.Std.WP.spec_ok out |>.mp h⟩
  | div => exact (Aeneas.Std.WP.spec_div.mp h).elim
  | vis e k => exact (Aeneas.Std.WP.spec_vis e k |>.mp h).elim
#print axioms unindent.Proofs.line_end_total_exact
