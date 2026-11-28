import Specs

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpec jsonptr

namespace JsonptrProofs

theorem indexForLen (idx : index.Index) (len : Usize) :
    ∃ out, idx.for_len len = .ok out ∧
      BoundsPost index.OutOfBoundsError.length index.OutOfBoundsError.index false idx len out := by
  cases idx <;> simp [index.Index.for_len, BoundsPost, indexValue]
  split <;> simp_all

theorem indexForLenInclusive (idx : index.Index) (len : Usize) :
    ∃ out, idx.for_len_incl len = .ok out ∧
      BoundsPost index.OutOfBoundsError.length index.OutOfBoundsError.index true idx len out := by
  cases idx <;> simp [index.Index.for_len_incl, BoundsPost, indexValue]
  split <;> simp_all

theorem indexForLenUnchecked (idx : jsonptr.index.Index) (len : Usize) :
    ∃ out, idx.for_len_unchecked len = .ok out ∧ out = indexValue idx len := by
  cases idx <;> simp [jsonptr.index.Index.for_len_unchecked, indexValue]

private def invariant (xs : List U8) (state : Usize × Usize × Usize) : Prop :=
  let (sep, tok, i) := state
  i.val ≤ xs.length ∧ sep.val + tok.val = i.val ∧
    xs[sep.val]? = some 47#u8 ∧
    (∀ k, sep.val < k → k < i.val → xs[k]? ≠ some 47#u8) ∧
    (∀ k, k < i.val → ¬ BadEscape xs k)

private theorem ordinary (xs : List U8) {sep tok i : Usize}
    (inv : invariant xs (sep, tok, i)) (hi : i.val < xs.length)
    (hslash : xs[i.val]? ≠ some 47#u8) (htilde : xs[i.val]? ≠ some 126#u8)
    {t' i' : Usize} (ht' : t'.val = tok.val + 1) (hi' : i'.val = i.val + 1) :
    invariant xs (sep, t', i') ∧ xs.length - i'.val < xs.length - i.val := by
  obtain ⟨hle, heq, hsep, hlast, hclean⟩ := inv
  refine ⟨⟨by omega, by omega, hsep, ?_, ?_⟩, by omega⟩
  · intro k hd hk
    by_cases hp : k < i.val
    · exact hlast k hd hp
    · obtain rfl : k = i.val := by omega
      exact hslash
  · intro k hk
    by_cases hp : k < i.val
    · exact hclean k hp
    · obtain rfl : k = i.val := by omega
      exact fun h => htilde h.1

private theorem separator (xs : List U8) {sep tok i : Usize}
    (inv : invariant xs (sep, tok, i)) (hi : i.val < xs.length)
    (hslash : xs[i.val]? = some 47#u8)
    {t' i' : Usize} (ht' : t'.val = 1) (hi' : i'.val = i.val + 1) :
    invariant xs (i, t', i') ∧ xs.length - i'.val < xs.length - i.val := by
  obtain ⟨_, _, _, _, hclean⟩ := inv
  refine ⟨⟨by omega, by omega, hslash, by intro k hd hk; omega, ?_⟩, by omega⟩
  intro k hk
  by_cases hp : k < i.val
  · exact hclean k hp
  · obtain rfl : k = i.val := by omega
    simp [BadEscape, hslash]

private theorem escaped (xs : List U8) {sep tok i : Usize}
    (inv : invariant xs (sep, tok, i)) (hi : i.val + 1 < xs.length)
    (htilde : xs[i.val]? = some 126#u8)
    (hnext : xs[i.val + 1]? = some 48#u8 ∨ xs[i.val + 1]? = some 49#u8)
    {t' i' : Usize} (ht' : t'.val = tok.val + 2) (hi' : i'.val = i.val + 2) :
    invariant xs (sep, t', i') ∧ xs.length - i'.val < xs.length - i.val := by
  obtain ⟨hle, heq, hsep, hlast, hclean⟩ := inv
  refine ⟨⟨by omega, by omega, hsep, ?_, ?_⟩, by omega⟩
  · intro k hd hk
    by_cases hp : k < i.val
    · exact hlast k hd hp
    · by_cases hc : k = i.val
      · subst k
        simp [htilde]
      · obtain rfl : k = i.val + 1 := by omega
        rcases hnext with h | h <;> simp [h]
  · intro k hk
    by_cases hp : k < i.val
    · exact hclean k hp
    · by_cases hc : k = i.val
      · subst k
        rcases hnext with h | h <;> simp [BadEscape, h]
      · obtain rfl : k = i.val + 1 := by omega
        rcases hnext with h | h <;> simp [BadEscape, h]

private theorem invalidEscape (xs : List U8) {sep tok i : Usize}
    (inv : invariant xs (sep, tok, i)) (hfirst : xs[0]? = some 47#u8)
    (hbad : BadEscape xs i.val) :
    ValidationPost xs (.Err (.InvalidEncoding sep ⟨tok, .Tilde⟩)) := by
  obtain ⟨_, heq, hsep, hlast, hclean⟩ := inv
  have hlt : sep.val < i.val := by
    by_contra! h
    have hsame : sep.val = i.val := by omega
    rw [hsame, hbad.1] at hsep
    simp at hsep
  exact ⟨hfirst, rfl, heq ▸ hbad, heq ▸ hclean, hsep, heq ▸ hlt, heq ▸ hlast⟩


private theorem slashLiteral : (47#8#uscalar : U8) = 47#u8 := by decide

private theorem tildeLiteral : (126#8#uscalar : U8) = 126#u8 := by decide

private theorem loopBody (bytes : Slice U8) (hfirst : bytes.val[0]? = some 47#u8)
    (sep tok i : Usize) (inv : invariant bytes.val (sep, tok, i)) :
    pointer.validate_bytes_loop0.body bytes sep tok i ⦃ r =>
      match r with
      | .done out => ValidationPost bytes.val out
      | .cont next => invariant bytes.val next ∧
          bytes.val.length - next.2.2.val < bytes.val.length - i.val ⦄ := by
  have hmax := Slice.length_ineq bytes
  have invFacts := inv
  obtain ⟨hle, hsum, _, _, hclean⟩ := invFacts
  simp only [pointer.validate_bytes_loop0.body]
  split
  next hlt =>
    have hi : i.val < bytes.val.length := by scalar_tac
    apply spec_bind (Slice.index_usize_spec bytes i hi)
    intro b hb
    have hb' : bytes.val[i.val]? = some b := by rw [List.getElem?_eq_getElem hi, hb]
    split
    next h =>
      step as ⟨i', hi'⟩
      step as ⟨t', ht'⟩
      exact separator bytes.val inv hi (by simpa [slashLiteral] using hb') ht' hi'
    next h =>
      have htilde : bytes.val[i.val]? = some 126#u8 := by simpa [slashLiteral, tildeLiteral] using hb'
      step as ⟨i1, hi1⟩
      split
      next hend =>
        have hnone : bytes.val[i.val + 1]? = none := by
          apply List.getElem?_eq_none
          scalar_tac
        exact (spec_ok _).mpr (invalidEscape _ inv hfirst ⟨htilde, by simp [hnone], by simp [hnone]⟩)
      next hcont =>
        have hnext : i1.val < bytes.val.length := by scalar_tac
        apply spec_bind (Slice.index_usize_spec bytes i1 hnext)
        intro x hx
        have hx' : bytes.val[i.val + 1]? = some x := by
          have hindex : i1.val = i.val + 1 := by scalar_tac
          rw [← hindex, List.getElem?_eq_getElem hnext, hx]
        split
        next hzero =>
          apply spec_bind (Slice.index_usize_spec bytes i1 hnext)
          intro y hy
          have hsame : y = x := hy.trans hx.symm
          rw [hsame]
          split
          next hone =>
            exact (spec_ok _).mpr
              (invalidEscape _ inv hfirst ⟨htilde, by simpa [hx'] using hzero,
                by simpa [hx'] using hone⟩)
          next hone =>
            have hone' : x = 49#u8 := by scalar_tac
            step as ⟨t1, ht1⟩
            step as ⟨i2, hi2⟩
            step as ⟨t2, ht2⟩
            exact escaped bytes.val inv (by scalar_tac) htilde
              (Or.inr (hx'.trans (congrArg some hone'))) (t' := t2) (i' := i2)
              (by scalar_tac) (by scalar_tac)
        next hzero =>
          have hzero' : x = 48#u8 := by scalar_tac
          step as ⟨t1, ht1⟩
          step as ⟨i2, hi2⟩
          step as ⟨t2, ht2⟩
          exact escaped bytes.val inv (by scalar_tac) htilde
            (Or.inl (hx'.trans (congrArg some hzero'))) (t' := t2) (i' := i2)
            (by scalar_tac) (by scalar_tac)
    next h hslash htilde =>
      step as ⟨i', hi'⟩
      step as ⟨t', ht'⟩
      exact ordinary bytes.val inv hi
        (by simpa [hb', slashLiteral] using hslash)
        (by simpa [hb', tildeLiteral] using htilde) ht' hi'
  next hstop =>
    apply (spec_ok _).mpr
    refine ⟨Or.inr hfirst, ?_⟩
    intro j hbad
    apply hclean j _ hbad
    have hj : j < bytes.val.length := List.getElem?_eq_some_iff.mp hbad.1 |>.choose
    scalar_tac

private theorem slashLoop (bytes : Slice U8) (hfirst : bytes.val[0]? = some 47#u8) :
    pointer.validate_bytes_loop1 bytes 0#usize 0#usize 0#usize ⦃ ValidationPost bytes.val ⦄ := by
  unfold pointer.validate_bytes_loop1
  apply loop.spec_decr_nat (fun state => bytes.val.length - state.2.2.val)
    (invariant bytes.val)
  · rintro ⟨sep, tok, i⟩ h
    change pointer.validate_bytes_loop0.body bytes sep tok i ⦃ _ ⦄
    apply spec_mono (loopBody bytes hfirst sep tok i h)
    intro r hr
    cases r <;> exact hr
  · refine ⟨by scalar_tac, by scalar_tac, ?_, ?_, ?_⟩
    · simpa using hfirst
    · intro k hk hlt
      scalar_tac
    · intro k hk
      scalar_tac

/-- Complete validation at the actual caller's zero offset, on nonempty slices. -/
theorem validateBytes (bytes : Slice U8) (h : 0 < bytes.val.length) :
    ∃ out, pointer.validate_bytes bytes 0#usize = .ok out ∧ ValidationPost bytes.val out := by
  have hwp : pointer.validate_bytes bytes 0#usize ⦃ ValidationPost bytes.val ⦄ := by
    unfold pointer.validate_bytes
    have hbound : (0#usize : Usize).val < bytes.val.length := by scalar_tac
    apply spec_bind (Slice.index_usize_spec bytes 0#usize hbound)
    intro b hb
    have hb' : bytes.val[0]? = some b := by
      have hget : bytes.val[(0#usize : Usize).val]? = some b := by
        rw [List.getElem?_eq_getElem hbound, hb]
      simpa using hget
    split
    next hnot =>
      apply (spec_ok _).mpr
      exact ⟨by intro hempty; simp [hempty] at h,
        by simpa [hb'] using hnot⟩
    next hslash =>
      have hfirst : bytes.val[0]? = some 47#u8 := by
        rw [hb']
        congr
        scalar_tac
      exact slashLoop bytes hfirst
  cases hresult : pointer.validate_bytes bytes 0#usize with
  | ret out => exact ⟨out, rfl, (spec_ok out).mp (hresult ▸ hwp)⟩
  | div => exact False.elim (spec_div.mp (hresult ▸ hwp))
  | vis e k => exact False.elim ((spec_vis e k).mp (hresult ▸ hwp))

end JsonptrProofs
