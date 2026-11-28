import ExtProofs.Tier2

/-!
# Section 9 proofs: range indexing (implementation agent)
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

/-- Byte offset of the separator opening token `k`. -/
def off (ts : List (List Nat)) (k : Nat) : Nat := (renderEncoded (ts.take k)).length

theorem off_succ (ts : List (List Nat)) (k : Nat) (t : List Nat) (h : ts[k]? = some t) :
    off ts (k + 1) = off ts k + (t.length + 1) := by
  simp [off, renderEncoded_take_succ ts k t h]

theorem off_le (ts : List (List Nat)) (k : Nat) : off ts k ≤ (renderEncoded ts).length := by
  unfold off
  conv_rhs => rw [← List.take_append_drop k ts, renderEncoded_append]
  simp

theorem list_sub {α : Type} (ts : List α) (a b : Nat) (hab : a ≤ b) :
    ts = ts.take a ++ (ts.drop a).take (b - a) ++ ts.drop b := by
  have h1 : ts.drop b = (ts.drop a).drop (b - a) := by rw [List.drop_drop]; congr 1; omega
  rw [h1, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem render_sub (ts : List (List Nat)) (a b : Nat) (hab : a ≤ b) :
    renderEncoded ts = renderEncoded (ts.take a) ++ renderEncoded ((ts.drop a).take (b - a)) ++
      renderEncoded (ts.drop b) := by
  rw [← renderEncoded_append, ← renderEncoded_append, ← list_sub ts a b hab]

theorem off_sub (ts : List (List Nat)) (a b : Nat) (hab : a ≤ b) :
    off ts b = off ts a + (renderEncoded ((ts.drop a).take (b - a))).length := by
  unfold off
  have : ts.take b = ts.take a ++ (ts.drop a).take (b - a) := by
    rw [show b = a + (b - a) by omega, List.take_add]; simp
  rw [this, renderEncoded_append]; simp

theorem slice_render (ts : List (List Nat)) (a b : Nat) (hab : a ≤ b) :
    (renderEncoded ts).slice (off ts a) (off ts b) = renderEncoded ((ts.drop a).take (b - a)) := by
  rw [List.slice, off_sub ts a b hab]
  conv_lhs => rw [render_sub ts a b hab]
  simp [off]

theorem rangeResult_none (xs : Slice U8) : RangeResult xs none none := by
  refine ⟨rfl, by simp [ValidPtrOpt, obytes], by simp⟩

theorem rangeResult_some (xs : Slice U8) (hv : ValidPtr xs) (v : Slice U8) (a b : Nat) (hab : a ≤ b)
    (hvb : bytes v = renderEncoded (((encodedTokens (bytes xs)).drop a).take (b - a))) :
    RangeResult xs (some v) (some (renderEncoded (((encodedTokens (bytes xs)).drop a).take (b - a)))) := by
  refine ⟨by simp [obytes, hvb], ?_, ?_⟩
  · intro r hr
    simp [obytes] at hr; rw [← hr, hvb]
    exact validPointer_of_tokOK _ (fun t ht => tokOK_of_validPointer _ hv t
      (List.mem_of_mem_drop (List.mem_of_mem_take ht)))
  · intro w hw
    simp at hw; subst hw
    rw [hvb]
    refine ⟨renderEncoded ((encodedTokens (bytes xs)).take a),
      renderEncoded ((encodedTokens (bytes xs)).drop b), ?_⟩
    rw [← render_sub _ a b hab, render_tokens_of_valid _ hv]

theorem bytes_slice_off (xs : Slice U8) (hv : ValidPtr xs) (s : Slice U8) (a b : Nat) (hab : a ≤ b)
    (hs : s.val = xs.val.slice (off (encodedTokens (bytes xs)) a) (off (encodedTokens (bytes xs)) b)) :
    bytes s = renderEncoded (((encodedTokens (bytes xs)).drop a).take (b - a)) := by
  rw [← slice_render _ a b hab, render_tokens_of_valid _ hv]
  simp [bytes, hs, List.slice, List.map_take, List.map_drop]

theorem len_le_max (xs : Slice U8) : (bytes xs).length ≤ Usize.max := by simp

/-- The invariant shared by the range loops over the iterator. -/
def RangeInv (ts : List (List Nat)) (ta : jsonptr.adapted_api.TokensAdapted) (cnt o : Nat) : Prop :=
  TokInv ta ∧ piecesOf ta = ts.drop cnt ∧ o = off ts cnt ∧ cnt ≤ ts.length

theorem next_none_end (ts : List (List Nat)) (ta : jsonptr.adapted_api.TokensAdapted) (cnt : Nat)
    (hp : piecesOf ta = ts.drop cnt) (hcnt : cnt ≤ ts.length)
    (ho : Option.map bytes none = (piecesOf ta).head?) : cnt = ts.length := by
  rw [hp] at ho
  by_contra hne
  cases h : ts.drop cnt with
  | nil => exact hne (by have := List.drop_eq_nil_iff.mp h; omega)
  | cons _ _ => rw [h] at ho; simp at ho

theorem next_some_tok (ts : List (List Nat)) (ta : jsonptr.adapted_api.TokensAdapted) (cnt : Nat)
    (s : Slice U8) (hp : piecesOf ta = ts.drop cnt)
    (ho : Option.map bytes (some s) = (piecesOf ta).head?) :
    ts[cnt]? = some (bytes s) ∧ cnt < ts.length := by
  rw [hp, List.head?_drop] at ho
  simp at ho
  exact ⟨ho.symm, (List.getElem?_eq_some_iff.mp ho.symm).1⟩

theorem getRangeFromAdapted : GetRangeFromContract := by
  intro xs st hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.get_range_from_adapted
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  set ts := encodedTokens (bytes xs) with hts
  have hX : renderEncoded ts = bytes xs := render_tokens_of_valid _ hv
  have hn : ts.length ≤ (bytes xs).length := encodedTokens_length_le _
  unfold jsonptr.adapted_api.get_range_from_adapted_loop
  apply loop.spec_decr_nat
    (fun p : Usize × Usize × jsonptr.adapted_api.TokensAdapted => ts.length - p.2.1.val)
    (fun p => RangeInv ts p.2.2 p.2.1.val p.1.val ∧ p.2.1.val ≤ st.val)
  · rintro ⟨o, cnt, ta⟩ ⟨⟨hia, hpa, hoff, hcnt⟩, hcs⟩
    simp only at hia hpa hoff hcnt hcs
    simp only [jsonptr.adapted_api.get_range_from_adapted_loop.body]
    step with tokensNext_spec ta hia as ⟨oo, ta1, ho, hp1, hi1, _⟩
    cases oo with
    | none =>
      have hend := next_none_end ts ta cnt.val hpa hcnt ho
      apply (spec_ok _).mpr
      have : getRangeFrom (bytes xs) st.val = none := by
        simp only [getRangeFrom, ← hts]; rw [if_neg]; omega
      rw [this]; exact rangeResult_none xs
    | some tok =>
      obtain ⟨htk, hlt⟩ := next_some_tok ts ta cnt.val tok hpa ho
      have hcb : cnt.val + 1 ≤ Usize.max := by have := len_le_max xs; omega
      step as ⟨c1, hc1⟩
      split
      next heq =>
        have hle : o.val ≤ xs.length := by
          have := off_le ts cnt.val; rw [hX, bytes_length] at this; rw [hoff]; exact this
        step as ⟨s1, hs1, _⟩
        have hcs' : cnt.val = st.val := by rw [heq]
        have hmodel : getRangeFrom (bytes xs) st.val =
            some (renderEncoded ((ts.drop st.val).take (ts.length - st.val))) := by
          have hst : st.val < ts.length := by omega
          simp [getRangeFrom, ← hts, hst]
          rw [List.take_of_length_le (by simp)]
        rw [hmodel]
        apply rangeResult_some xs hv s1 st.val ts.length (by omega)
        rw [← hcs', ← slice_render ts cnt.val ts.length hcnt, hX]
        have : off ts ts.length = (bytes xs).length := by simp [off, hX]
        rw [this, ← hoff]
        simp [bytes, hs1, List.slice, List.map_drop]
      next hne =>
        have hsucc := off_succ ts cnt.val (bytes tok) htk
        have hle := off_le ts (cnt.val + 1)
        rw [hX, hsucc] at hle
        have htl : tok.length + 1 ≤ Usize.max := by
          have : (bytes tok).length = tok.length := bytes_length tok
          have := len_le_max xs; omega
        step as ⟨l1, hl1⟩
        have hb2 : o.val + l1.val ≤ Usize.max := by
          have : (bytes tok).length = tok.length := bytes_length tok
          have := len_le_max xs; scalar_tac
        step as ⟨o5, ho5⟩
        have hne' : cnt.val ≠ st.val := fun e => hne (by scalar_tac)
        refine ⟨⟨hi1, ?_, ?_, by scalar_tac⟩, by scalar_tac, by scalar_tac⟩
        · rw [hp1, hpa, List.tail_drop]; congr 1; scalar_tac
        · have hbt : (bytes tok).length = (↑tok : List U8).length := by simp [bytes]
          rw [show c1.val = cnt.val + 1 by scalar_tac, hsucc, hbt, ← hoff]; scalar_tac
  · exact ⟨⟨hinv, by simp [hp], by simp [off, renderEncoded], by simp⟩, by simp⟩

theorem spec_bind_ok {α β : Type} (v : α) (f : α → Result β) (Q : β → Prop) (h : f v ⦃ Q ⦄) :
    (do let y ← Result.ok v; f y) ⦃ Q ⦄ := by
  apply spec_bind ((spec_ok v).mpr rfl : Result.ok v ⦃ fun y => y = v ⦄)
  intro y hy; rw [hy]; exact h

theorem spec_bind_ite_ok {α β : Type} (c : Prop) [Decidable c] (a b : α) (f : α → Result β)
    (Q : β → Prop) (h : f (if c then a else b) ⦃ Q ⦄) :
    (do let y ← (if c then Result.ok a else Result.ok b); f y) ⦃ Q ⦄ := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h ⊢; exact spec_bind_ok _ _ _ h
  · simp only [hc, ↓reduceIte] at h ⊢; exact spec_bind_ok _ _ _ h

theorem off_mono (ts : List (List Nat)) (a b : Nat) (hab : a ≤ b) : off ts a ≤ off ts b := by
  rw [off_sub ts a b hab]; omega

theorem off_zero (ts : List (List Nat)) : off ts 0 = 0 := by simp [off, renderEncoded]

theorem off_len (xs : Slice U8) (hv : ValidPtr xs) :
    off (encodedTokens (bytes xs)) (encodedTokens (bytes xs)).length = (bytes xs).length := by
  simp [off, render_tokens_of_valid _ hv]

theorem off_le_len (xs : Slice U8) (hv : ValidPtr xs) (k : Nat) :
    off (encodedTokens (bytes xs)) k ≤ xs.length := by
  have := off_le (encodedTokens (bytes xs)) k
  rwa [render_tokens_of_valid _ hv, bytes_length] at this

theorem getRangeToAdapted : GetRangeToContract := by
  intro xs e hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.get_range_to_adapted
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  set ts := encodedTokens (bytes xs) with hts
  have hX : renderEncoded ts = bytes xs := render_tokens_of_valid _ hv
  have hn : ts.length ≤ (bytes xs).length := encodedTokens_length_le _
  have hlx := len_le_max xs
  have hxl : xs.length ≤ Usize.max := by scalar_tac
  have hmodel : ∀ k, k ≤ ts.length → getRangeTo (bytes xs) k =
      some (renderEncoded ((ts.drop 0).take (k - 0))) := by
    intro k hk; simp [getRangeTo, ← hts, hk]
  unfold jsonptr.adapted_api.get_range_to_adapted_loop
  apply loop.spec_decr_nat
    (fun p : Usize × Usize × jsonptr.adapted_api.TokensAdapted => ts.length - p.1.val)
    (fun p => RangeInv ts p.2.2 p.1.val p.2.1.val ∧ p.1.val ≤ e.val)
  · rintro ⟨idx, o, ta⟩ ⟨⟨hia, hpa, hoff, hcnt⟩, hce⟩
    simp only at hia hpa hoff hcnt hce
    simp only [jsonptr.adapted_api.get_range_to_adapted_loop.body]
    step with tokensNext_spec ta hia as ⟨oo, ta1, ho, hp1, hi1, _⟩
    cases oo with
    | none =>
      have hend := next_none_end ts ta idx.val hpa hcnt ho
      by_cases heq : idx = e
      · simp only [heq, ↓reduceIte]; apply spec_bind_ok
        have hle : o.val ≤ xs.length := by rw [hoff]; exact off_le_len xs hv _
        step as ⟨s1, hs1, _⟩
        have he : e.val = ts.length := by rw [← heq]; exact hend
        rw [hmodel e.val (by omega)]
        apply rangeResult_some xs hv s1 0 e.val (by omega)
        apply bytes_slice_off xs hv s1 0 e.val (by omega)
        rw [off_zero, he, off_len xs hv, ← hX]; rw [hX, ← off_len xs hv, ← hend, ← hoff]
        exact hs1
      · simp only [heq, ↓reduceIte]; apply spec_bind_ok
        have hne := heq
        refine (spec_ok _).mpr ?_
        show RangeResult xs none (getRangeTo (bytes xs) e.val)
        have : getRangeTo (bytes xs) e.val = none := by
          have : ¬ e.val ≤ ts.length := by
            intro h; apply hne; scalar_tac
          simp [getRangeTo, ← hts, this]
        rw [this]; exact rangeResult_none xs
    | some tok =>
      obtain ⟨htk, hlt⟩ := next_some_tok ts ta idx.val tok hpa ho
      by_cases heq : idx = e
      · simp only [heq, ↓reduceIte]
        have hle : o.val ≤ xs.length := by rw [hoff]; exact off_le_len xs hv _
        apply spec_bind (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec { «end» := o } xs hle)
        rintro s1 ⟨hs1, _⟩
        apply (spec_ok _).mpr
        have he : idx.val = e.val := by rw [heq]
        rw [hmodel e.val (by omega)]
        apply rangeResult_some xs hv s1 0 e.val (by omega)
        apply bytes_slice_off xs hv s1 0 e.val (by omega)
        rw [off_zero, ← he, ← hoff]; exact hs1
      · simp only [heq, ↓reduceIte]
        have hne := heq
        have hsucc := off_succ ts idx.val (bytes tok) htk
        have hle := off_le_len xs hv (idx.val + 1)
        rw [hsucc] at hle
        have hbt : (bytes tok).length = tok.length := bytes_length tok
        have hcb : idx.val + 1 ≤ Usize.max := by omega
        step as ⟨c1, hc1⟩
        have htl : tok.length + 1 ≤ Usize.max := by omega
        step as ⟨l1, hl1⟩
        have hb2 : o.val + l1.val ≤ Usize.max := by scalar_tac
        step as ⟨o5, ho5⟩
        have hne' : idx.val ≠ e.val := fun h => hne (by scalar_tac)
        refine ⟨⟨hi1, ?_, ?_, by scalar_tac⟩, by scalar_tac, by scalar_tac⟩
        · rw [hp1, hpa, List.tail_drop]; congr 1; scalar_tac
        · have hbt' : (bytes tok).length = (↑tok : List U8).length := by simp [bytes]
          rw [show c1.val = idx.val + 1 by scalar_tac, hsucc, hbt', ← hoff]; scalar_tac
  · exact ⟨⟨hinv, by simp [hp], by simp [off, renderEncoded], by simp⟩, by simp⟩

theorem getRangeToInclusiveAdapted : GetRangeToInclusiveContract := by
  intro xs e hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.get_range_to_inclusive_adapted
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  set ts := encodedTokens (bytes xs) with hts
  have hX : renderEncoded ts = bytes xs := render_tokens_of_valid _ hv
  have hn : ts.length ≤ (bytes xs).length := encodedTokens_length_le _
  have hlx := len_le_max xs
  have hxl : xs.length ≤ Usize.max := by scalar_tac
  unfold jsonptr.adapted_api.get_range_to_inclusive_adapted_loop
  apply loop.spec_decr_nat
    (fun p : Usize × Usize × jsonptr.adapted_api.TokensAdapted => ts.length - p.2.1.val)
    (fun p => RangeInv ts p.2.2 p.2.1.val p.1.val ∧ p.2.1.val ≤ e.val)
  · rintro ⟨o, cnt, ta⟩ ⟨⟨hia, hpa, hoff, hcnt⟩, hce⟩
    simp only at hia hpa hoff hcnt hce
    simp only [jsonptr.adapted_api.get_range_to_inclusive_adapted_loop.body]
    step with tokensNext_spec ta hia as ⟨oo, ta1, ho, hp1, hi1, _⟩
    cases oo with
    | none =>
      have hend := next_none_end ts ta cnt.val hpa hcnt ho
      apply (spec_ok _).mpr
      have : getRangeToIncl (bytes xs) e.val = none := by
        have : ¬ e.val < count (bytes xs) := by simp [count, ← hts]; omega
        simp [getRangeToIncl, this]
      rw [this]; exact rangeResult_none xs
    | some tok =>
      obtain ⟨htk, hlt⟩ := next_some_tok ts ta cnt.val tok hpa ho
      have hsucc := off_succ ts cnt.val (bytes tok) htk
      have hle := off_le_len xs hv (cnt.val + 1)
      rw [hsucc] at hle
      have hbt : (bytes tok).length = tok.length := bytes_length tok
      have hcb : cnt.val + 1 ≤ Usize.max := by omega
      step as ⟨c1, hc1⟩
      have htl : tok.length + 1 ≤ Usize.max := by omega
      step as ⟨l1, hl1⟩
      have hb2 : o.val + l1.val ≤ Usize.max := by scalar_tac
      step as ⟨o5, ho5⟩
      have ho5' : o5.val = off ts (cnt.val + 1) := by
        have hbt' : (bytes tok).length = (↑tok : List U8).length := by simp [bytes]
        rw [hsucc, hbt', ← hoff]; scalar_tac
      split
      next heq =>
        have he : cnt.val = e.val := by rw [heq]
        step as ⟨s1, hs1, _⟩
        have hm : getRangeToIncl (bytes xs) e.val =
            some (renderEncoded ((ts.drop 0).take (e.val + 1 - 0))) := by
          have h1 : e.val < count (bytes xs) := by simp [count, ← hts]; omega
          have h2 : e.val + 1 ≤ ts.length := by omega
          simp [getRangeToIncl, h1, getRangeTo, ← hts, h2]
        rw [hm]
        apply rangeResult_some xs hv s1 0 (e.val + 1) (by omega)
        apply bytes_slice_off xs hv s1 0 (e.val + 1) (by omega)
        rw [off_zero, ← he, ← ho5']; exact hs1
      next hne =>
        have hne' : cnt.val ≠ e.val := fun h => hne (by scalar_tac)
        apply (spec_ok _).mpr
        refine ⟨?_, by scalar_tac, by scalar_tac⟩
        refine ⟨hi1, ?_, by rw [ho5']; congr 1; scalar_tac, by scalar_tac⟩
        rw [hp1, hpa, List.tail_drop]; congr 1; scalar_tac
  · exact ⟨⟨hinv, by simp [hp], by simp [off, renderEncoded], by simp⟩, by simp⟩

theorem getRangeFullAdapted : GetRangeFullContract := by
  intro xs hv
  refine ⟨some xs, rfl, by simp [obytes], ?_, ?_⟩
  · intro r hr; simp [obytes] at hr; rw [← hr]; exact hv
  · intro v hv'; simp at hv'; subst hv'; exact ⟨[], [], by simp⟩

/-- The recorded start offset: set once the start token has been passed. -/
def SoInv (ts : List (List Nat)) (s idx : Nat) (so : Option Usize) : Prop :=
  so.map (fun x => x.val) = if s < idx then some (off ts s) else none

theorem getRangeAdapted : GetRangeContract := by
  intro xs st en hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.get_range_adapted
  split
  next hlt =>
    apply (spec_ok _).mpr
    have : getRange (bytes xs) st.val en.val = none := by
      simp only [getRange]; rw [if_neg]; intro h; have := h.1; scalar_tac
    rw [this]; exact rangeResult_none xs
  next hge =>
  have hse : st.val ≤ en.val := by scalar_tac
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  set ts := encodedTokens (bytes xs) with hts
  have hX : renderEncoded ts = bytes xs := render_tokens_of_valid _ hv
  have hn : ts.length ≤ (bytes xs).length := encodedTokens_length_le _
  have hlx := len_le_max xs
  have hxl : xs.length ≤ Usize.max := by scalar_tac
  unfold jsonptr.adapted_api.get_range_adapted_loop
  apply loop.spec_decr_nat
    (fun p : Usize × Usize × Option Usize × Slice U8 × Usize × Bool => ts.length - p.1.val)
    (fun p => RangeInv ts ⟨p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩ p.1.val p.2.1.val ∧ p.1.val ≤ en.val ∧
      SoInv ts st.val p.1.val p.2.2.1)
  · rintro ⟨idx, o, so, hay, stt, fin⟩ ⟨⟨hia, hpa, hoff, hcnt⟩, hce, hso⟩
    simp only at hia hpa hoff hcnt hce hso
    simp only [jsonptr.adapted_api.get_range_adapted_loop.body]
    step with tokensNext_spec _ hia as ⟨oo, ta1, ho, hp1, hi1, _⟩
    cases oo with
    | none =>
      have hend := next_none_end ts _ idx.val hpa hcnt ho
      by_cases heq : idx = en
      · simp only [heq, ↓reduceIte]
        apply spec_bind_ok
        cases so with
        | none =>
          apply (spec_ok _).mpr
          simp only [SoInv, Option.map_none] at hso
          have hns : ¬ st.val < idx.val := by intro h; rw [if_pos h] at hso; simp at hso
          have : getRange (bytes xs) st.val en.val = none := by
            simp only [getRange, ← hts]; rw [if_neg]; intro h; omega
          rw [this]; exact rangeResult_none xs
        | some sv =>
          simp only [SoInv, Option.map_some] at hso
          have hsl : st.val < idx.val := by
            by_contra h; rw [if_neg h] at hso; simp at hso
          rw [if_pos hsl] at hso; simp at hso
          have he : en.val = ts.length := by rw [← heq]; exact hend
          have hle1 : sv.val ≤ o.val := by
            rw [hso, hoff]; exact off_mono ts _ _ (by omega)
          have hle2 : o.val ≤ xs.length := by rw [hoff]; exact off_le_len xs hv _
          apply spec_bind (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec { start := sv, «end» := o } xs hle1 hle2)
          rintro s1 ⟨hs1, _⟩
          apply (spec_ok _).mpr
          have hm : getRange (bytes xs) st.val en.val =
              some (renderEncoded ((ts.drop st.val).take (en.val - st.val))) := by
            simp only [getRange, ← hts]; rw [if_pos ⟨hse, by omega, by omega⟩]
          rw [hm]
          apply rangeResult_some xs hv s1 st.val en.val hse
          apply bytes_slice_off xs hv s1 st.val en.val hse
          rw [← hso, he, ← hend, ← hoff]; exact hs1
      · simp only [heq, ↓reduceIte]
        apply spec_bind_ok
        have hne : idx.val ≠ en.val := fun h => heq (by scalar_tac)
        cases so with
        | none =>
          apply (spec_ok _).mpr
          have : getRange (bytes xs) st.val en.val = none := by
            simp only [getRange, ← hts]; rw [if_neg]; intro h; omega
          rw [this]; exact rangeResult_none xs
        | some sv =>
          apply (spec_ok _).mpr
          have : getRange (bytes xs) st.val en.val = none := by
            simp only [getRange, ← hts]; rw [if_neg]; intro h; omega
          rw [this]; exact rangeResult_none xs
    | some tok =>
      obtain ⟨htk, hlt⟩ := next_some_tok ts _ idx.val tok hpa ho
      apply spec_bind_ite_ok
      have hso2 : SoInv ts st.val (idx.val + 1) (if idx = st then some o else so) := by
        by_cases hst : idx = st
        · simp only [hst, ↓reduceIte, SoInv, Option.map_some]
          rw [if_pos (by omega)]; rw [hoff, hst]
        · simp only [hst, ↓reduceIte]
          have hst' : idx.val ≠ st.val := fun h => hst (by scalar_tac)
          simp only [SoInv] at hso ⊢
          rw [hso]
          by_cases h1 : st.val < idx.val
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (by omega)]
      generalize (if idx = st then some o else so) = o2 at hso2 ⊢
      by_cases heq : idx = en
      · have he : idx.val = en.val := by rw [heq]
        have hsl : st.val < idx.val + 1 := by omega
        have hso2' := hso2
        simp only [SoInv] at hso2'; rw [if_pos hsl] at hso2'
        obtain ⟨sv, rfl, hsv⟩ : ∃ sv, o2 = some sv ∧ sv.val = off ts st.val := by
          cases o2 with
          | none => simp at hso2'
          | some sv => simp at hso2'; exact ⟨sv, rfl, hso2'⟩
        rw [if_pos heq]
        show (do let s1 ← core.slice.index.SliceIndexRangeUsizeSlice.index { start := sv, «end» := o } xs
                 Result.ok (ControlFlow.done (some s1))) ⦃ _ ⦄
        have hle1 : sv.val ≤ o.val := by rw [hsv, hoff]; exact off_mono ts _ _ (by omega)
        have hle2 : o.val ≤ xs.length := by rw [hoff]; exact off_le_len xs hv _
        apply spec_bind (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec { start := sv, «end» := o } xs hle1 hle2)
        rintro s1 ⟨hs1, _⟩
        apply (spec_ok _).mpr
        have hm : getRange (bytes xs) st.val en.val =
            some (renderEncoded ((ts.drop st.val).take (en.val - st.val))) := by
          simp only [getRange, ← hts]; rw [if_pos ⟨hse, by omega, by omega⟩]
        show RangeResult xs (some s1) (getRange (bytes xs) st.val en.val)
        rw [hm]
        apply rangeResult_some xs hv s1 st.val en.val hse
        apply bytes_slice_off xs hv s1 st.val en.val hse
        rw [← hsv, ← he, ← hoff]; exact hs1
      · simp only [heq, ↓reduceIte]
        have hne : idx.val ≠ en.val := fun h => heq (by scalar_tac)
        have hsucc := off_succ ts idx.val (bytes tok) htk
        have hle := off_le_len xs hv (idx.val + 1)
        rw [hsucc] at hle
        have hbt : (bytes tok).length = tok.length := bytes_length tok
        have hcb : idx.val + 1 ≤ Usize.max := by omega
        step as ⟨c1, hc1⟩
        have htl : tok.length + 1 ≤ Usize.max := by omega
        step as ⟨l1, hl1⟩
        have hb2 : o.val + l1.val ≤ Usize.max := by scalar_tac
        step as ⟨o5, ho5⟩
        have ho5' : o5.val = off ts (idx.val + 1) := by
          have hbt' : (bytes tok).length = (↑tok : List U8).length := by simp [bytes]
          rw [hsucc, hbt', ← hoff]; scalar_tac
        have hc1' : c1.val = idx.val + 1 := by scalar_tac
        refine ⟨⟨hi1, ?_, by rw [ho5', hc1'], by omega⟩, by omega, by rw [hc1']; exact hso2, by omega⟩
        rw [hp1, hpa, List.tail_drop, hc1']
  · exact ⟨⟨hinv, by simp [hp], by simp [off, renderEncoded], by simp⟩, by simp, by simp [SoInv]⟩

theorem getRangeInclusiveAdapted : GetRangeInclusiveContract := by
  intro xs st en hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.get_range_inclusive_adapted
  split
  next hlt =>
    apply (spec_ok _).mpr
    have : getRangeIncl (bytes xs) st.val en.val = none := by
      simp only [getRangeIncl]; rw [if_neg]; intro h; have := h.1; scalar_tac
    rw [this]; exact rangeResult_none xs
  next hge =>
  have hse : st.val ≤ en.val := by scalar_tac
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  set ts := encodedTokens (bytes xs) with hts
  have hX : renderEncoded ts = bytes xs := render_tokens_of_valid _ hv
  have hn : ts.length ≤ (bytes xs).length := encodedTokens_length_le _
  have hlx := len_le_max xs
  have hxl : xs.length ≤ Usize.max := by scalar_tac
  unfold jsonptr.adapted_api.get_range_inclusive_adapted_loop
  apply loop.spec_decr_nat
    (fun p : Usize × Option Usize × Usize × Slice U8 × Usize × Bool => ts.length - p.2.2.1.val)
    (fun p => RangeInv ts ⟨p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩ p.2.2.1.val p.1.val ∧ p.2.2.1.val ≤ en.val ∧
      SoInv ts st.val p.2.2.1.val p.2.1)
  · rintro ⟨o, so, cnt, hay, stt, fin⟩ ⟨⟨hia, hpa, hoff, hcnt⟩, hce, hso⟩
    simp only at hia hpa hoff hcnt hce hso
    simp only [jsonptr.adapted_api.get_range_inclusive_adapted_loop.body]
    step with tokensNext_spec _ hia as ⟨oo, ta1, ho, hp1, hi1, _⟩
    cases oo with
    | none =>
      have hend := next_none_end ts _ cnt.val hpa hcnt ho
      have hm : getRangeIncl (bytes xs) st.val en.val = none := by
        have : ¬ en.val < count (bytes xs) := by simp [count, ← hts]; omega
        simp [getRangeIncl, this]
      cases so with
      | none => apply (spec_ok _).mpr; rw [hm]; exact rangeResult_none xs
      | some _ => apply (spec_ok _).mpr; rw [hm]; exact rangeResult_none xs
    | some tok =>
      obtain ⟨htk, hlt⟩ := next_some_tok ts _ cnt.val tok hpa ho
      have hsucc := off_succ ts cnt.val (bytes tok) htk
      have hle := off_le_len xs hv (cnt.val + 1)
      rw [hsucc] at hle
      have hbt : (bytes tok).length = tok.length := bytes_length tok
      have hcb : cnt.val + 1 ≤ Usize.max := by omega
      step as ⟨c1, hc1⟩
      apply spec_bind_ite_ok
      have hso2 : SoInv ts st.val (cnt.val + 1) (if cnt = st then some o else so) := by
        by_cases hst : cnt = st
        · simp only [hst, ↓reduceIte, SoInv, Option.map_some]
          rw [if_pos (by omega)]; rw [hoff, hst]
        · simp only [hst, ↓reduceIte]
          have hst' : cnt.val ≠ st.val := fun h => hst (by scalar_tac)
          simp only [SoInv] at hso ⊢
          rw [hso]
          by_cases h1 : st.val < cnt.val
          · rw [if_pos h1, if_pos (by omega)]
          · rw [if_neg h1, if_neg (by omega)]
      generalize (if cnt = st then some o else so) = o2 at hso2 ⊢
      have htl : tok.length + 1 ≤ Usize.max := by omega
      step as ⟨l1, hl1⟩
      have hb2 : o.val + l1.val ≤ Usize.max := by scalar_tac
      step as ⟨o6, ho6⟩
      have ho6' : o6.val = off ts (cnt.val + 1) := by
        have hbt' : (bytes tok).length = (↑tok : List U8).length := by simp [bytes]
        rw [hsucc, hbt', ← hoff]; scalar_tac
      by_cases heq : cnt = en
      · have he : cnt.val = en.val := by rw [heq]
        have hsl : st.val < cnt.val + 1 := by omega
        have hso2' := hso2
        simp only [SoInv] at hso2'; rw [if_pos hsl] at hso2'
        obtain ⟨sv, rfl, hsv⟩ : ∃ sv, o2 = some sv ∧ sv.val = off ts st.val := by
          cases o2 with
          | none => simp at hso2'
          | some sv => simp at hso2'; exact ⟨sv, rfl, hso2'⟩
        rw [if_pos heq]
        show (do let s1 ← core.slice.index.SliceIndexRangeUsizeSlice.index { start := sv, «end» := o6 } xs
                 Result.ok (ControlFlow.done (some s1))) ⦃ _ ⦄
        have hle1 : sv.val ≤ o6.val := by rw [hsv, ho6']; exact off_mono ts _ _ (by omega)
        have hle2 : o6.val ≤ xs.length := by rw [ho6']; exact off_le_len xs hv _
        apply spec_bind (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec { start := sv, «end» := o6 } xs hle1 hle2)
        rintro s1 ⟨hs1, _⟩
        apply (spec_ok _).mpr
        have hm : getRangeIncl (bytes xs) st.val en.val =
            some (renderEncoded ((ts.drop st.val).take (en.val + 1 - st.val))) := by
          have h1 : en.val < count (bytes xs) := by simp [count, ← hts]; omega
          simp only [getRangeIncl, h1, hse, and_self, ↓reduceIte, getRange, ← hts]
          rw [if_pos ⟨by omega, by omega, by omega⟩]
        show RangeResult xs (some s1) (getRangeIncl (bytes xs) st.val en.val)
        rw [hm]
        apply rangeResult_some xs hv s1 st.val (en.val + 1) (by omega)
        apply bytes_slice_off xs hv s1 st.val (en.val + 1) (by omega)
        rw [← hsv, ← he, ← ho6']; exact hs1
      · rw [if_neg heq]
        have hne : cnt.val ≠ en.val := fun h => heq (by scalar_tac)
        apply (spec_ok _).mpr
        dsimp only
        have hc1' : c1.val = cnt.val + 1 := by scalar_tac
        refine ⟨⟨hi1, ?_, by rw [ho6', hc1'], by omega⟩, by omega, by rw [hc1']; exact hso2, by omega⟩
        rw [hp1, hpa, List.tail_drop, hc1']
  · exact ⟨⟨hinv, by simp [hp], by simp [off, renderEncoded], by simp⟩, by simp, by simp [SoInv]⟩

end JsonptrExtProofs
