import Proofs.Common
import Proofs.Model

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

theorem findSlash_spec (s : Slice U8) :
    jsonptr.pointer.find_slash_adapted s ⦃ FirstIdx (fun b => b = 47#u8) s.val ⦄ := by
  unfold jsonptr.pointer.find_slash_adapted jsonptr.pointer.find_slash_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ (k : Nat) x, k < i.val → s.val[k]? = some x → x ≠ 47#u8)
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.pointer.find_slash_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi)
      intro x hx
      have hx' : s.val[i.val]? = some x := by rw [List.getElem?_eq_getElem hi, hx]
      split
      next heq =>
        apply (spec_ok _).mpr
        exact ⟨⟨x, hx', heq⟩, hall⟩
      next hne =>
        step as ⟨i', hi'⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k y hk hy
        by_cases hki : k < i.val
        · exact hall k y hki hy
        · have : k = i.val := by scalar_tac
          subst this
          rw [hx'] at hy; cases hy; exact hne
    next hge =>
      apply (spec_ok _).mpr
      intro k y hy
      have : k < s.val.length := (List.getElem?_eq_some_iff.mp hy).1
      exact hall k y (by scalar_tac) hy
  · exact ⟨by scalar_tac, fun k x hk => by scalar_tac⟩

theorem notMem_map_take (l : List U8) (j : Nat) (c : U8)
    (h : ∀ (k : Nat) x, k < j → l[k]? = some x → x ≠ c) :
    c.val ∉ (l.take j).map (fun b => b.val) := by
  intro hm
  obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
  have hkj : k < j := by
    have := (List.getElem?_eq_some_iff.mp hk).1; simp at this; omega
  rw [List.getElem?_take, if_pos hkj] at hk
  exact h k x hkj hk (UScalar.eq_of_val_eq hxv)

theorem notMem_map (l : List U8) (c : U8) (h : ∀ (k : Nat) x, l[k]? = some x → x ≠ c) :
    c.val ∉ l.map (fun b => b.val) := by
  intro hm
  obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
  exact h k x hk (UScalar.eq_of_val_eq hxv)

/-- Target 6, `Pointer::split_front` (and so `tokens`). -/
theorem splitFrontAdapted : SplitFrontContract := by
  intro xs hpre
  by_cases hlen : xs.length = 0
  · have hnil : xs.val = [] := List.length_eq_zero_iff.mp hlen
    refine ⟨none, ?_, ?_⟩
    · simp [jsonptr.pointer.split_front_adapted, core.slice.Slice.is_empty, hlen]
    · simp [bytes, hnil]
  · obtain ⟨a, rest, hxs⟩ : ∃ a rest, xs.val = a :: rest := by
      cases h : xs.val with
      | nil => simp [Slice.length, h] at hlen
      | cons a rest => exact ⟨a, rest, rfl⟩
    have ha : a.val = 47 := by
      rcases hpre with h | h <;> simp [bytes, hxs] at h; exact h
    have hb : bytes xs = 47 :: rest.map (fun b => b.val) := by simp [bytes, hxs, ha]
    have hs1 : (xs.drop 1#usize).val = rest := by simp [hxs]
    obtain ⟨o, ho, hfirst⟩ := ok_of_spec (findSlash_spec (xs.drop 1#usize))
    rw [hs1] at hfirst
    have hindex : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) xs
        { start := 1#usize } = .ok (xs.drop 1#usize) := by
      simp [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice.index]
      scalar_tac
    cases o with
    | none =>
      refine ⟨some (xs.drop 1#usize, Array.to_slice (Std.Array.empty U8)), ?_, ?_⟩
      · simp only [jsonptr.pointer.split_front_adapted, core.slice.Slice.is_empty]
        simp [hlen, hindex, ho, lift]
      · have h47 := notMem_map rest 47#u8 hfirst
        have hemp : bytes (Array.to_slice (Std.Array.empty U8)) = [] := by
          simp [bytes, Array.to_slice, Std.Array.empty]
        have hb1 : bytes (xs.drop 1#usize) = rest.map (fun b => b.val) := by simp [bytes, hs1]
        dsimp only
        rw [hemp, hb1, hb]
        refine ⟨by simp, h47, Or.inl rfl, ?_⟩
        simpa using Model.encodedTokens_cons (rest.map (fun b => b.val)) [] h47 (Or.inl rfl)
    | some j =>
      obtain ⟨⟨x, hx, hx47⟩, hbefore⟩ := hfirst
      have hj : j.val < rest.length := (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨p, hp, hpv⟩ := ok_of_spec (core.slice.Slice.split_at.spec (xs.drop 1#usize) j
        (by simp [hs1]; omega))
      obtain ⟨tok, rem⟩ := p
      simp only [uncurry'] at hpv
      obtain ⟨_, _, htok, hrem⟩ := hpv
      refine ⟨some (tok, rem), ?_, ?_⟩
      · simp only [jsonptr.pointer.split_front_adapted, core.slice.Slice.is_empty]
        simp [hlen, hindex, ho, hp]
      · dsimp only
        rw [hs1] at htok hrem
        have hbt : bytes tok = (rest.take j.val).map (fun b => b.val) := by simp [bytes, htok]
        have hbr : bytes rem = (rest.drop j.val).map (fun b => b.val) := by simp [bytes, hrem]
        have h47 : 47 ∉ bytes tok := by
          rw [hbt]; exact notMem_map_take rest j.val 47#u8 hbefore
        have hremh : bytes rem = [] ∨ (bytes rem).head? = some 47 := by
          right; rw [hbr, List.head?_map, List.head?_drop, hx]; simp [hx47]
        have hcat : bytes xs = 47 :: (bytes tok ++ bytes rem) := by
          rw [hb, hbt, hbr, ← List.map_append, List.take_append_drop]
        refine ⟨hcat, h47, hremh, ?_⟩
        rw [hcat]; exact Model.encodedTokens_cons _ _ h47 hremh

end JsonptrAdaptedProofs
