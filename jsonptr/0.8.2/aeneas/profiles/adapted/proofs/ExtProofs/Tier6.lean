import ExtProofs.Tier56

/-! # Tier 6: byte order and component order (implementation agent) -/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem bytesLt_append (p x y : List Nat) : bytesLt (p ++ x) (p ++ y) = bytesLt x y := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [bytesLt, ih]

theorem bytesLt_nil_cons (b : Nat) (y : List Nat) : bytesLt [] (b :: y) = true := rfl

theorem decomp_idx (l : List Nat) (i : Nat) (h : i < l.length) :
    l = l.take i ++ l[i] :: l.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop i l, List.drop_eq_getElem_cons h]

theorem strCmp_spec (a b : Slice U8) :
    jsonptr.adapted_api.str_cmp_adapted a b ⦃ o => OrderingAgrees o (bytes a) (bytes b) ⦄ := by
  simp only [jsonptr.adapted_api.str_cmp_adapted]
  apply spec_bind_ite_ok
  generalize hn : (if a.len < b.len then a.len else b.len) = n
  have hn1 : n.val ≤ a.length ∧ n.val ≤ b.length ∧ (n.val = a.length ∨ n.val = b.length) := by
    rw [← hn]; split <;> scalar_tac
  unfold jsonptr.adapted_api.str_cmp_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => n.val - i.val)
    (fun i => i.val ≤ n.val ∧ (bytes a).take i.val = (bytes b).take i.val)
  · rintro i ⟨hle, htk⟩
    simp only [jsonptr.adapted_api.str_cmp_adapted_loop.body]
    split
    next hlt =>
      have hia : i.val < a.length := by scalar_tac
      have hib : i.val < b.length := by scalar_tac
      step as ⟨x, hx⟩
      step as ⟨y, hy⟩
      have hxa : (bytes a)[i.val]'(by simpa using hia) = x.val := by simp [bytes, hx]
      have hyb : (bytes b)[i.val]'(by simpa using hib) = y.val := by simp [bytes, hy]
      split
      next hxy =>
        apply (spec_ok _).mpr
        show bytesLt (bytes a) (bytes b) = true
        have hlt' : x.val < y.val := by scalar_tac
        rw [decomp_idx (bytes a) i.val (by simpa using hia), decomp_idx (bytes b) i.val (by simpa using hib),
          htk, bytesLt_append, hxa, hyb]
        simp [bytesLt, hlt']
      next hxy =>
        split
        next hgt =>
          apply (spec_ok _).mpr
          show bytesLt (bytes b) (bytes a) = true
          have hlt' : y.val < x.val := by scalar_tac
          rw [decomp_idx (bytes a) i.val (by simpa using hia), decomp_idx (bytes b) i.val (by simpa using hib),
            htk, bytesLt_append, hxa, hyb]
          simp [bytesLt, hlt']
        next hng =>
          have heq : x.val = y.val := by scalar_tac
          step as ⟨i4, hi4⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [show i4.val = i.val + 1 by scalar_tac, List.take_succ, List.take_succ, htk,
            List.getElem?_eq_getElem (show i.val < (bytes a).length by simpa using hia),
            List.getElem?_eq_getElem (show i.val < (bytes b).length by simpa using hib), hxa, hyb, heq]
    next hge =>
      have hin : i.val = n.val := by scalar_tac
      rw [hin] at htk
      split
      next hlab =>
        apply (spec_ok _).mpr
        show bytesLt (bytes a) (bytes b) = true
        have han : n.val = a.length := by scalar_tac
        have hbl : n.val < b.length := by scalar_tac
        have e1 : bytesLt (bytes a) (bytes b) =
            bytesLt ((bytes b).take n.val ++ []) ((bytes b).take n.val ++ (bytes b).drop n.val) := by
          rw [List.take_append_drop, List.append_nil, ← htk, List.take_of_length_le (by rw [bytes_length]; omega)]
        rw [e1, bytesLt_append]
        cases h : (bytes b).drop n.val with
        | nil => have := List.drop_eq_nil_iff.mp h; rw [bytes_length] at this; omega
        | cons _ _ => rfl
      next hnl =>
        split
        next hgab =>
          apply (spec_ok _).mpr
          show bytesLt (bytes b) (bytes a) = true
          have hbn : n.val = b.length := by scalar_tac
          have hal : n.val < a.length := by scalar_tac
          have e1 : bytesLt (bytes b) (bytes a) =
              bytesLt ((bytes a).take n.val ++ []) ((bytes a).take n.val ++ (bytes a).drop n.val) := by
            rw [List.take_append_drop, List.append_nil, htk, List.take_of_length_le (by rw [bytes_length]; omega)]
          rw [e1, bytesLt_append]
          cases h : (bytes a).drop n.val with
          | nil => have := List.drop_eq_nil_iff.mp h; rw [bytes_length] at this; omega
          | cons _ _ => rfl
        next hng =>
          apply (spec_ok _).mpr
          show bytes a = bytes b
          have h1 : (bytes a).take n.val = bytes a := List.take_of_length_le (by rw [bytes_length]; scalar_tac)
          have h2 : (bytes b).take n.val = bytes b := List.take_of_length_le (by rw [bytes_length]; scalar_tac)
          rw [← h1, ← h2, htk]
  · exact ⟨by simp, by simp⟩

theorem strCmpAdapted : StrCmpContract := fun a b => ok_of_spec (strCmp_spec a b)

theorem strPartialCmpAdapted : StrPartialCmpContract := by
  intro a b
  obtain ⟨o, ho, hm⟩ := ok_of_spec (strCmp_spec a b)
  exact ⟨o, ho, by simp [jsonptr.adapted_api.str_partial_cmp_adapted, ho], hm⟩

theorem componentCmpAdapted : ComponentCmpContract := by
  intro a b
  cases a with
  | Root => cases b <;> simp [jsonptr.adapted_api.component_cmp_adapted, component, componentLt]
  | Token x =>
    cases b with
    | Root => simp [jsonptr.adapted_api.component_cmp_adapted, component, componentLt]
    | Token y =>
      obtain ⟨o, ho, hm⟩ := ok_of_spec (strCmp_spec x y)
      refine ⟨o, by simp [jsonptr.adapted_api.component_cmp_adapted, ho], ?_⟩
      cases o <;> simp [OrderingAgrees] at hm <;> simp [component, componentLt, hm]

end JsonptrExtProofs
