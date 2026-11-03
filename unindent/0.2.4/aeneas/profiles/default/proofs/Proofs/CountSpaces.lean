import Unindent
open Aeneas Aeneas.Std Result ControlFlow Error WP
namespace UnindentProof
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U8)
def Blank (b : U8) : Prop := b = 32#u8 ∨ b = 9#u8
def CountSpacesPost (s : Slice U8) (r : Option Usize) : Prop :=
  match r with
  | none => ∀ j (h : j < s.val.length), Blank s.val[j]!
  | some n => ∃ h : n.val < s.val.length,
      ¬ Blank s.val[n.val] ∧ ∀ j (hj : j < n.val), Blank s.val[j]!
def Inv (s : Slice U8) (it : Iter) : Prop :=
  it.iter.slice = s ∧ it.iter.i = it.count.val ∧ it.iter.i ≤ s.val.length ∧
  ∀ j (_h : j < it.iter.i), Blank s.val[j]!

theorem countSpacesLoop_spec (s : Slice U8) (it : Iter) (hi : Inv s it) :
    unindent.unindent.count_spaces_loop it ⦃ CountSpacesPost s ⦄ := by
  unfold unindent.unindent.count_spaces_loop
  apply loop.spec_decr_nat (fun x : Iter ↦ s.val.length - x.iter.i) (Inv s)
  · intro x hx
    rcases hx with ⟨hs, hc, hb, hp⟩
    unfold unindent.unindent.count_spaces_loop.body
    by_cases hlt : x.iter.i < s.val.length
    · have hin : (core.iter.traits.iterator.IteratorSliceIter U8).next x.iter
          ⦃ p => p.1 = some s.val[x.iter.i] ∧
            p.2 = { x.iter with i := x.iter.i + 1 } ⦄ := by
        simp [core.slice.iter.IteratorSliceIter.next, hs, hlt, Slice.len, WP.spec_ok]
      have hnext := core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
        (core.iter.traits.iterator.IteratorSliceIter U8) x s.val[x.iter.i]
        { x.iter with i := x.iter.i + 1 } hin (by have := s.length_ineq; omega)
      apply WP.spec_bind hnext
      rintro ⟨opt, y⟩ ⟨ho, hy, hcount⟩
      subst opt
      change (if s.val[x.iter.i] != 32#u8 then
        if s.val[x.iter.i] != 9#u8 then ok (done (some x.count)) else ok (cont y)
        else ok (cont y)) ⦃ _ ⦄
      simp only [bne_iff_ne]
      split <;> rename_i h32
      · split <;> rename_i h9
        · simp only [WP.spec_ok]
          unfold CountSpacesPost
          exact ⟨by omega, by simpa [Blank, hc] using And.intro h32 h9, by simpa [hc] using hp⟩
        · simp only [WP.spec_ok]
          unfold Inv
          constructor
          · refine ⟨by simpa [hy] using hs, by simp [hy]; omega, by simp [hy]; omega, ?_⟩
            intro j hj
            simp only [hy] at hj
            by_cases hj' : j < x.iter.i
            · exact hp j hj'
            · have he : j = x.iter.i := by omega
              subst j
              simp [Blank, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt, not_not.mp h9]
          · simp [hy]; omega
      · simp only [WP.spec_ok]
        unfold Inv
        constructor
        · refine ⟨by simpa [hy] using hs, by simp [hy]; omega, by simp [hy]; omega, ?_⟩
          intro j hj
          simp only [hy] at hj
          by_cases hj' : j < x.iter.i
          · exact hp j hj'
          · have he : j = x.iter.i := by omega
            subst j
            simp [Blank, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt, not_not.mp h32]
        · simp [hy]; omega
    · have hin : (core.iter.traits.iterator.IteratorSliceIter U8).next x.iter
          ⦃ p => p.1 = none ∧ p.2 = x.iter ⦄ := by
        simp [core.slice.iter.IteratorSliceIter.next, hs, hlt, Slice.len, WP.spec_ok]
      apply WP.spec_bind (core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
        (core.iter.traits.iterator.IteratorSliceIter U8) x x.iter hin)
      rintro ⟨opt, y⟩ ⟨ho, hy, hcount⟩
      subst opt
      change ok (done none : ControlFlow Iter (Option Usize)) ⦃ _ ⦄
      simp only [WP.spec_ok]
      unfold CountSpacesPost
      intro j hj
      exact hp j (by omega)
  · exact hi

theorem countSpaces_spec (s : Slice U8) :
    unindent.unindent.count_spaces s ⦃ CountSpacesPost s ⦄ := by
  unfold unindent.unindent.count_spaces core.slice.Slice.iter
    core.iter.traits.iterator.Iterator.enumerate.trait_default
    core.iter.traits.iterator.Iterator.enumerate.default
  simp only [bind_ok]
  apply countSpacesLoop_spec
  exact ⟨rfl, rfl, Nat.zero_le _, by intro j hj; change j < 0 at hj; omega⟩
unseal Result in
theorem countSpaces_total_exact (s : Slice U8) :
    ∃ out, unindent.unindent.count_spaces s = ok out ∧ CountSpacesPost s out := by
  have h := countSpaces_spec s
  generalize he : unindent.unindent.count_spaces s = m at h ⊢
  cases m using Aeneas.Data.Coinductive.ITree.cases with
  | ret out => exact ⟨out, rfl, WP.spec_ok out |>.mp h⟩
  | div => exact (WP.spec_div.mp h).elim
  | vis e k => exact (WP.spec_vis e k |>.mp h).elim
#print axioms countSpaces_total_exact
end UnindentProof
