import Statements.Tier2Nav
import ExtProofs.Tokens
import ExtProofs.Helpers

/-!
# Tier 2 proofs (specification sections 8-11), implementation agent
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem splitSlash_length_le (l : List Nat) : (splitSlash l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [splitSlash]
  | cons x r ih =>
    simp only [splitSlash]
    split
    · simp; omega
    · split
      · simp
      · next p ps heq => rw [heq] at ih; simp at ih ⊢; omega

theorem encodedTokens_length_le (xs : List Nat) : (encodedTokens xs).length ≤ xs.length := by
  have := splitSlash_length_le xs
  simp [encodedTokens]; omega

theorem seqThenNone_cons {α : Type} (p : α) (ps : List α) (k : Nat) :
    seqThenNone (p :: ps) (k + 1) = some p :: seqThenNone ps k := by
  simp only [seqThenNone, List.map_cons, List.cons_append, List.take_succ_cons, List.cons.injEq,
    true_and]
  rw [List.take_append, List.take_append, List.take_replicate, List.take_replicate]
  congr 2; omega

theorem seqThenNone_nil {α : Type} (k : Nat) :
    seqThenNone ([] : List α) (k + 1) = none :: seqThenNone [] k := by
  simp [seqThenNone, List.take_replicate, List.replicate_succ]

theorem runTokens_spec (k : Nat) : ∀ it, TokInv it →
    ∃ os, runTokens k it = .ok os ∧ os.map (Option.map bytes) = seqThenNone (piecesOf it) k ∧
      ∀ t, some t ∈ os → bytes t ∈ piecesOf it := by
  induction k with
  | zero => intro it _; exact ⟨[], rfl, by simp [seqThenNone], by simp⟩
  | succ k ih =>
    intro it hinv
    obtain ⟨⟨o, it'⟩, hnext, ho, hp, hinv', _⟩ := ok_of_spec (tokensNext_spec it hinv)
    obtain ⟨os, hos, hmap, hmem⟩ := ih it' hinv'
    refine ⟨o :: os, by simp [runTokens, hnext, hos], ?_, ?_⟩
    · cases hpc : piecesOf it with
      | nil =>
        rw [hpc] at ho hp
        cases o with
        | none => simp [hmap, hp, seqThenNone_nil]
        | some _ => simp at ho
      | cons p ps =>
        rw [hpc] at ho hp
        cases o with
        | none => simp at ho
        | some t => simp at ho; simp [hmap, hp, seqThenNone_cons, ho]
    · intro t ht
      rcases List.mem_cons.mp ht with h | h
      · subst h
        cases hpc : piecesOf it with
        | nil => rw [hpc] at ho; simp at ho
        | cons p ps => rw [hpc] at ho; simp at ho; simp [ho]
      · have := hmem t h; rw [hp] at this; exact List.mem_of_mem_tail this

theorem tokensAdapted : TokensContract := by
  intro xs hv
  obtain ⟨it, hit, hp, hinv, _⟩ := ok_of_spec (tokens_spec xs)
  refine ⟨it, hit, fun k => ?_⟩
  obtain ⟨os, hos, hmap, hmem⟩ := runTokens_spec k it hinv
  refine ⟨os, hos, by rw [hmap, hp], fun t ht => ?_⟩
  have := hmem t ht; rw [hp] at this
  exact validEncodedToken_of_valid_mem _ _ hv this

theorem countAdapted : CountContract := by
  intro xs hv
  have hle : count (bytes xs) ≤ Usize.max := by
    have h1 := encodedTokens_length_le (bytes xs)
    have h2 : xs.length ≤ Usize.max := by scalar_tac
    simp only [count, bytes_length] at *; omega
  apply ok_of_spec
  unfold jsonptr.adapted_api.count_adapted
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  unfold jsonptr.adapted_api.count_adapted_loop
  apply loop.spec_decr_nat (fun p : jsonptr.adapted_api.TokensAdapted × Usize => (piecesOf p.1).length)
    (fun p => TokInv p.1 ∧ p.2.val + (piecesOf p.1).length = count (bytes xs))
  · rintro ⟨ta, i⟩ ⟨hinv, hsum⟩
    simp only at hinv hsum
    simp only [jsonptr.adapted_api.count_adapted_loop.body]
    apply spec_bind (tokensNext_spec ta hinv)
    rintro ⟨o, ta1⟩ ⟨ho, hp1, hinv1, _⟩
    cases o with
    | none =>
      simp
      cases hpc : piecesOf ta with
      | nil => rw [hpc] at hsum; simp at hsum; omega
      | cons p ps => rw [hpc] at ho; simp at ho
    | some t =>
      cases hpc : piecesOf ta with
      | nil => rw [hpc] at ho; simp at ho
      | cons p ps =>
        rw [hpc] at hsum hp1
        simp only [List.length_cons] at hsum
        step as ⟨i1, hi1⟩
        refine ⟨hinv1, ?_, ?_⟩
        · rw [hp1]; simp; omega
        · simp [hp1]
  · exact ⟨hinv, by simp [hp, count]⟩

/-! ## Navigation by the last or first slash -/

theorem decomp_at (l : List Nat) (i : Nat) (h47 : l[i]? = some 47) :
    l = l.take i ++ 47 :: l.drop (i + 1) := by
  have hi : i < l.length := (List.getElem?_eq_some_iff.mp h47).1
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons hi]
  congr 2
  rw [List.getElem?_eq_getElem hi] at h47; simpa using h47

theorem noSlash_after (l : List Nat) (i : Nat) (hlast : ∀ k, i < k → l[k]? ≠ some 47) :
    47 ∉ l.drop (i + 1) := by
  intro hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
  rw [List.getElem?_drop] at hk
  exact hlast (i + 1 + k) (by omega) hk

theorem noSlash_before (l : List Nat) (j : Nat) (hfirst : ∀ k, k < j → l[k]? ≠ some 47) :
    47 ∉ l.take j := by
  intro hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
  have hk' := hk
  rw [List.getElem?_take] at hk'
  split at hk'
  · exact hfirst k (by omega) hk'
  · simp at hk'

theorem valid_noSlash_nil (xs : List Nat) (hv : ValidPointer xs) (h : 47 ∉ xs) : xs = [] := by
  rcases slashLed_of_valid xs hv with h' | h'
  · exact h'
  · cases xs with
    | nil => rfl
    | cons x r => simp at h'; subst h'; exact absurd List.mem_cons_self h

/-- A valid pointer split at its last slash. -/
theorem lastSlash_model (X : List Nat) (hv : ValidPointer X) (i : Nat) (h47 : X[i]? = some 47)
    (hlast : ∀ k, i < k → X[k]? ≠ some 47) :
    encodedTokens X = encodedTokens (X.take i) ++ [X.drop (i + 1)] ∧ ValidPointer (X.take i) ∧
      47 ∉ X.drop (i + 1) := by
  have hd := decomp_at X i h47
  have hns := noSlash_after X i hlast
  have hvs := (valid_split (X.take i) (47 :: X.drop (i + 1)) (hd ▸ hv) (Or.inr rfl)).1
  refine ⟨?_, hvs, hns⟩
  conv_lhs => rw [hd]
  exact encodedTokens_last _ _ hns (slashLed_of_valid _ hvs)

theorem backAdapted : BackContract := by
  intro xs hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.back_adapted
  apply spec_bind (rfindSlash_spec xs)
  intro o ho
  cases o with
  | none =>
    have hnil := valid_noSlash_nil _ hv ho
    apply (spec_ok _).mpr
    refine ⟨by simp [obytes, back, hnil, encodedTokens_nil], by simp [ValidTokOpt, obytes]⟩
  | some i =>
    obtain ⟨hi, h47, hlast⟩ := ho
    obtain ⟨htok, _, hns⟩ := lastSlash_model _ hv i.val h47 hlast
    step as ⟨i1, hi1⟩
    step as ⟨s, hs, _⟩
    have hbs : bytes s = (bytes xs).drop (i.val + 1) := by simp [bytes, hs, List.map_drop, hi1]
    refine ⟨by simp [obytes, back, htok, hbs], ?_⟩
    intro r hr
    simp [obytes] at hr; subst hr
    exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok, hbs]; simp)

theorem splitBackAdapted : SplitBackContract := by
  intro xs hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.split_back_adapted
  apply spec_bind (rfindSlash_spec xs)
  intro o ho
  cases o with
  | none =>
    have hnil := valid_noSlash_nil _ hv ho
    apply (spec_ok _).mpr
    refine ⟨by simp [opbytes, splitBack, hnil, encodedTokens_nil], by simp⟩
  | some i =>
    obtain ⟨hi, h47, hlast⟩ := ho
    obtain ⟨htok, hvh, hns⟩ := lastSlash_model _ hv i.val h47 hlast
    step as ⟨s, hs, _⟩
    step as ⟨i1, hi1⟩
    step as ⟨s1, hs1, _⟩
    have hbs : bytes s = (bytes xs).take i.val := by simp [bytes, hs, List.map_take]
    have hbs1 : bytes s1 = (bytes xs).drop (i.val + 1) := by simp [bytes, hs1, List.map_drop, hi1]
    refine ⟨?_, ?_⟩
    · simp only [opbytes, Option.map_some, splitBack, htok, hbs, hbs1, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_concat]
      rw [render_tokens_of_valid _ hvh]
    · intro h t ht
      simp at ht; obtain ⟨rfl, rfl⟩ := ht
      refine ⟨by simpa [ValidPtr, hbs] using hvh, ?_, ?_⟩
      · exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok, hbs1]; simp)
      · rw [hbs, hbs1]; exact decomp_at _ _ h47

theorem parentAdapted : ParentContract := by
  intro xs hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.parent_adapted
  apply spec_bind (rfindSlash_spec xs)
  intro o ho
  cases o with
  | none =>
    have hnil := valid_noSlash_nil _ hv ho
    apply (spec_ok _).mpr
    refine ⟨by simp [obytes, parent, splitBack, hnil, encodedTokens_nil], by simp [ValidPtrOpt, obytes]⟩
  | some i =>
    obtain ⟨hi, h47, hlast⟩ := ho
    obtain ⟨htok, hvh, hns⟩ := lastSlash_model _ hv i.val h47 hlast
    step as ⟨s, hs, _⟩
    have hbs : bytes s = (bytes xs).take i.val := by simp [bytes, hs, List.map_take]
    refine ⟨?_, ?_⟩
    · simp only [obytes, Option.map_some, parent, splitBack, htok, hbs, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_concat, Option.map_some]
      rw [render_tokens_of_valid _ hvh]
    · intro r hr; simp [obytes] at hr; subst hr; simpa [hbs] using hvh

theorem frontAdapted : FrontContract := by
  intro xs hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.front_adapted
  step as ⟨b, hb⟩
  split
  next hemp =>
    have hnil : bytes xs = [] := by
      have : xs.length = 0 := by simpa [hb] using hemp
      simpa [bytes] using this
    apply (spec_ok _).mpr
    refine ⟨by simp [obytes, front, hnil, encodedTokens_nil], by simp [ValidTokOpt, obytes]⟩
  next hne =>
    have hlen : 1 ≤ xs.length := by
      have : ¬ xs.length = 0 := by simpa [hb] using hne
      scalar_tac
    obtain ⟨r, hr⟩ : ∃ r, bytes xs = 47 :: r := by
      rcases slashLed_of_valid _ hv with h | h
      · have h0 : (bytes xs).length = 0 := by rw [h]; rfl
        rw [bytes_length] at h0; omega
      · cases hx : bytes xs with
        | nil => rw [hx] at h; simp at h
        | cons x r => rw [hx] at h; simp at h; exact ⟨r, by rw [h]⟩
    step as ⟨s, hs, _⟩
    have hbs : bytes s = r := by
      have : bytes s = (bytes xs).drop 1 := by simp [bytes, hs, List.map_drop]
      rw [this, hr]; rfl
    apply spec_bind (findSlash_spec s)
    intro o ho
    cases o with
    | none =>
      apply (spec_ok _).mpr
      have hns : 47 ∉ r := hbs ▸ ho
      have htok : encodedTokens (bytes xs) = [r] := by
        rw [hr, encodedTokens_slash, splitSlash_noSlash r hns]
      refine ⟨by simp [obytes, front, htok, hbs], ?_⟩
      intro t ht; simp [obytes] at ht; subst ht
      exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok, hbs]; simp)
    | some j =>
      obtain ⟨hj, hj47, hfirst⟩ := ho
      step as ⟨s1, hs1, _⟩
      have hbs1 : bytes s1 = r.take j.val := by
        rw [← hbs]; simp [bytes, hs1, List.map_take]
      rw [hbs] at hj47 hfirst
      have hd := decomp_at r j.val hj47
      have hns := noSlash_before r j.val hfirst
      have htok : encodedTokens (bytes xs) = r.take j.val :: encodedTokens (47 :: r.drop (j.val + 1)) := by
        rw [hr]; conv_lhs => rw [hd]
        exact encodedTokens_cons_split _ _ hns (Or.inr rfl)
      refine ⟨by simp [obytes, front, htok, hbs1], ?_⟩
      intro t ht; simp [obytes] at ht; subst ht
      exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok, hbs1]; simp)

theorem componentFromTokenAdapted : ComponentFromTokenContract := by
  intro t _
  exact ⟨_, rfl, rfl⟩

/-! ## `get(usize)` through `advance_by` -/

/-- Postcondition of `advance_by_adapted`. -/
def AdvPost (P : List (List Nat)) (n : Nat) : core.result.Result Unit Usize × jsonptr.adapted_api.TokensAdapted → Prop
  | (.Ok _, it') => TokInv it' ∧ n ≤ P.length ∧ piecesOf it' = P.drop n
  | (.Err _, _) => P.length < n

theorem advanceBy_spec (it : jsonptr.adapted_api.TokensAdapted) (n : Usize) (hinv : TokInv it) :
    jsonptr.adapted_api.advance_by_adapted it n ⦃ AdvPost (piecesOf it) n.val ⦄ := by
  unfold jsonptr.adapted_api.advance_by_adapted jsonptr.adapted_api.advance_by_adapted_loop
  apply loop.spec_decr_nat (fun p : jsonptr.adapted_api.TokensAdapted × Usize => n.val - p.2.val)
    (fun p => TokInv p.1 ∧ p.2.val ≤ n.val ∧ p.2.val ≤ (piecesOf it).length ∧
      piecesOf p.1 = (piecesOf it).drop p.2.val)
  · rintro ⟨ta, i⟩ ⟨hinv', hle, hlen, hp⟩
    simp only at hinv' hle hlen hp
    simp only [jsonptr.adapted_api.advance_by_adapted_loop.body]
    split
    next hlt =>
      step with tokensNext_spec ta hinv' as ⟨o, ta1, ho, hp1, hinv1, _⟩
      cases o with
      | none =>
        simp only [core.option.Option.is_none, Option.isNone_none, ↓reduceIte]
        step as ⟨d, hd⟩
        simp only [AdvPost]
        rw [hp] at ho
        have : (piecesOf it).drop i.val = [] := by
          cases h : (piecesOf it).drop i.val with
          | nil => rfl
          | cons _ _ => rw [h] at ho; simp at ho
        have := List.drop_eq_nil_iff.mp this
        scalar_tac
      | some t =>
        simp only [core.option.Option.is_none, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
        rw [hp] at ho hp1
        have hne : (piecesOf it).drop i.val ≠ [] := by intro h; rw [h] at ho; simp at ho
        have hlt' : i.val < (piecesOf it).length := by
          by_contra hc; exact hne (List.drop_eq_nil_iff.mpr (by omega))
        step as ⟨i1, hi1⟩
        refine ⟨hinv1, by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        rw [hp1, hi1, List.tail_drop]
    next hge =>
      apply (spec_ok _).mpr
      have : i.val = n.val := by scalar_tac
      exact ⟨hinv', by omega, by rw [hp, this]⟩
  · exact ⟨hinv, by simp, by simp, by simp⟩

theorem getIndexAdapted : GetIndexContract := by
  intro xs i hv
  apply ok_of_spec
  unfold jsonptr.adapted_api.get_index_adapted
  apply spec_bind (tokens_spec xs)
  rintro it ⟨hp, hinv, _⟩
  apply spec_bind (advanceBy_spec it i hinv)
  rintro ⟨r, ta1⟩ hadv
  cases r with
  | Ok u =>
    obtain ⟨hinv1, hle, hp1⟩ := hadv
    apply spec_bind (tokensNext_spec ta1 hinv1)
    rintro ⟨o, ta2⟩ ⟨ho, _, _, _⟩
    apply (spec_ok _).mpr
    rw [hp1, hp] at ho
    have hget : getToken (bytes xs) i.val = ((encodedTokens (bytes xs)).drop i.val).head? := by
      simp [getToken, List.head?_drop]
    refine ⟨by rw [obytes, ho, hget], ?_⟩
    intro t ht
    simp only [obytes] at ht; rw [ho] at ht
    exact validEncodedToken_of_valid_mem _ _ hv (List.mem_of_mem_drop (List.mem_of_mem_head? ht))
  | Err e =>
    apply (spec_ok _).mpr
    have hlt : (encodedTokens (bytes xs)).length < i.val := by rw [← hp]; exact hadv
    refine ⟨by simp [obytes, getToken]; omega, by simp [ValidTokOpt, obytes]⟩

/-! ## Components -/

/-- The components a `Components` state still yields. -/
def compPieces (c : jsonptr.adapted_api.ComponentsAdapted) : List Component :=
  (if c.sent_root then [] else [Component.root]) ++ (piecesOf c.tokens).map Component.token

theorem componentsNext_spec (c : jsonptr.adapted_api.ComponentsAdapted) (hinv : TokInv c.tokens) :
    jsonptr.adapted_api.components_next_adapted c ⦃ (o : Option jsonptr.adapted_api.ComponentAdapted) c' =>
      o.map component = (compPieces c).head? ∧ compPieces c' = (compPieces c).tail ∧ TokInv c'.tokens ∧
      (∀ t, o = some (.Token t) → bytes t ∈ piecesOf c.tokens) ∧
      piecesOf c'.tokens ⊆ piecesOf c.tokens ⦄ := by
  unfold jsonptr.adapted_api.components_next_adapted
  split
  next hs =>
    apply spec_bind (tokensNext_spec c.tokens hinv)
    rintro ⟨o, ta⟩ ⟨ho, hp, hinv', _⟩
    cases o with
    | none =>
      apply (spec_ok _).mpr
      cases h : piecesOf c.tokens with
      | nil => refine ⟨by simp [compPieces, hs, h], by simp [compPieces, hs, h, hp], hinv', by simp, by simp [hp, h]⟩
      | cons _ _ => rw [h] at ho; simp at ho
    | some t =>
      apply (spec_ok _).mpr
      cases h : piecesOf c.tokens with
      | nil => rw [h] at ho; simp at ho
      | cons p ps =>
        rw [h] at ho hp; simp at ho
        refine ⟨by simp [compPieces, hs, h, component, ho], by simp [compPieces, hs, h, hp], hinv', ?_, ?_⟩
        · intro u hu; simp at hu; subst hu; simp [ho]
        · intro x hx; rw [hp] at hx; simp; exact Or.inr hx
  next hs =>
    apply (spec_ok _).mpr
    refine ⟨by simp [compPieces, hs, component], by simp [compPieces, hs], hinv, by simp, by simp⟩

theorem runComponents_spec (k : Nat) : ∀ c, TokInv c.tokens →
    ∃ os, runComponents k c = .ok os ∧ os.map (Option.map component) = seqThenNone (compPieces c) k ∧
      ∀ t, some (jsonptr.adapted_api.ComponentAdapted.Token t) ∈ os → bytes t ∈ piecesOf c.tokens := by
  induction k with
  | zero => intro c _; exact ⟨[], rfl, by simp [seqThenNone], by simp⟩
  | succ k ih =>
    intro c hinv
    obtain ⟨⟨o, c'⟩, hnext, ho, hp, hinv', htok, hsub⟩ := ok_of_spec (componentsNext_spec c hinv)
    obtain ⟨os, hos, hmap, hmem⟩ := ih c' hinv'
    refine ⟨o :: os, by simp [runComponents, hnext, hos], ?_, ?_⟩
    · cases hpc : compPieces c with
      | nil =>
        rw [hpc] at ho hp
        cases o with
        | none => simp [hmap, hp, seqThenNone_nil]
        | some _ => simp at ho
      | cons p ps =>
        rw [hpc] at ho hp
        cases o with
        | none => simp at ho
        | some t => simp at ho; simp [hmap, hp, seqThenNone_cons, ho]
    · intro t ht
      rcases List.mem_cons.mp ht with h | h
      · exact htok t h.symm
      · exact hsub (hmem t h)

theorem componentsAdapted : ComponentsContract := by
  intro xs hv
  obtain ⟨it, hit, hp, hinv, _⟩ := ok_of_spec (tokens_spec xs)
  refine ⟨{ tokens := it, sent_root := false }, by simp [jsonptr.adapted_api.components_adapted, hit], ?_⟩
  intro k
  obtain ⟨os, hos, hmap, hmem⟩ := runComponents_spec k { tokens := it, sent_root := false } hinv
  refine ⟨os, hos, ?_, ?_⟩
  · rw [hmap]; simp [compPieces, components, hp]
  · intro t ht
    have := hmem t ht; simp only at this; rw [hp] at this
    exact validEncodedToken_of_valid_mem _ _ hv this

/-! ## Section 10: byte split -/

theorem splitAtOffset_spec (xs : Slice U8) (off : Usize) :
    jsonptr.adapted_api.split_at_offset_adapted xs off ⦃ r =>
      opbytes r = splitAtOffset (bytes xs) off.val ⦄ := by
  simp only [jsonptr.adapted_api.split_at_offset_adapted]
  split
  next hlt =>
    have hi : off.val < xs.length := by scalar_tac
    step as ⟨x, hx⟩
    have hx' : (bytes xs)[off.val]? = some x.val := by
      rw [bytes_getElem?, List.getElem?_eq_getElem hi, hx]; rfl
    split
    next h47 =>
      step as ⟨s0, s1, _, _, h0, h1⟩
      simp only [opbytes, Option.map_some, splitAtOffset, hx']
      simp [bytes, h0, h1, List.map_take, List.map_drop]
      rfl
    next hne =>
      have hx47 : x.val ≠ 47 := by
        intro e; apply hne; exact (u8_eq_47 x).mpr e
      simp [opbytes, splitAtOffset, hx', hx47]
  next hge =>
    have : xs.length ≤ off.val := by scalar_tac
    have hn : (bytes xs)[off.val]? = none := List.getElem?_eq_none (by simpa using this)
    simp [opbytes, splitAtOffset, hn]

theorem splitAtOffsetAdapted : SplitAtOffsetContract := by
  intro xs off hv
  obtain ⟨r, hr, hm⟩ := ok_of_spec (splitAtOffset_spec xs off)
  refine ⟨r, hr, hm, ?_⟩
  intro h t ht
  subst ht
  simp only [opbytes, Option.map_some, splitAtOffset] at hm
  split at hm
  next h47 =>
    simp at hm
    obtain ⟨hh, ht⟩ := hm
    have hd := decomp_at _ _ h47
    have hvs := valid_split ((bytes xs).take off.val) ((bytes xs).drop off.val)
      (by rw [List.take_append_drop]; exact hv)
      (Or.inr (by rw [List.head?_drop]; exact h47))
    exact ⟨by rw [ValidPtr, hh]; exact hvs.1, by rw [ValidPtr, ht]; exact hvs.2⟩
  next => simp at hm

/-! ## Section 11: prefix and suffix operations -/

theorem head?_eq_of_append (O R : List Nat) (h : O.length < (O ++ R).length) :
    (O ++ R)[O.length]? = R.head? := by
  rw [List.getElem?_append_right (le_refl _)]; simp [List.head?_eq_getElem?]

/-- The token prefix test equals a byte prefix that ends at a separator. -/
theorem startsWith_iff (X O : List Nat) (hX : ValidPointer X) (hO : ValidPointer O) :
    startsWith X O = true ↔ ∃ R, X = O ++ R ∧ (R = [] ∨ R.head? = some 47) := by
  unfold startsWith
  rw [isTokenPrefix_iff]
  constructor
  · rintro ⟨vs, hvs⟩
    refine ⟨renderEncoded vs, ?_, renderEncoded_head vs⟩
    rw [← render_tokens_of_valid X hX, hvs, renderEncoded_append, render_tokens_of_valid O hO]
  · rintro ⟨R, rfl, hR⟩
    exact ⟨encodedTokens R, encodedTokens_append O R (slashLed_of_valid O hO) hR⟩

theorem prefixSep_iff (X O : List Nat) :
    (O <+: X ∧ (O.length = X.length ∨ X[O.length]? = some 47)) ↔
      ∃ R, X = O ++ R ∧ (R = [] ∨ R.head? = some 47) := by
  constructor
  · rintro ⟨⟨R, rfl⟩, h⟩
    refine ⟨R, rfl, ?_⟩
    rcases h with h | h
    · left; simpa using h
    · right
      by_cases hR : R = []
      · subst hR; simp at h
      · rwa [head?_eq_of_append O R (by simp; exact List.length_pos_of_ne_nil hR)] at h
  · rintro ⟨R, rfl, hR⟩
    refine ⟨⟨R, rfl⟩, ?_⟩
    rcases hR with h | h
    · left; simp [h]
    · right
      have hne : R ≠ [] := by intro e; subst e; simp at h
      rw [head?_eq_of_append O R (by simp; exact List.length_pos_of_ne_nil hne)]; exact h

theorem startsWithAdapted : StartsWithContract := by
  intro xs other hv ho
  apply ok_of_spec
  unfold jsonptr.adapted_api.starts_with_adapted
  apply spec_bind (startsWithExt_spec xs other)
  intro b hb
  have key := (startsWith_iff (bytes xs) (bytes other) hv ho).trans (prefixSep_iff _ _).symm
  split
  next hbt =>
    have hpre : bytes other <+: bytes xs := hb.mp hbt
    dsimp only
    split
    next heq =>
      apply (spec_ok _).mpr
      have hl : (bytes other).length = (bytes xs).length := by simp; scalar_tac
      exact (key.mpr ⟨hpre, Or.inl hl⟩).symm
    next hne =>
      have hl : other.length < xs.length := by
        have := hpre.length_le; simp only [bytes_length] at this
        have : other.length ≠ xs.length := by intro e; apply hne; scalar_tac
        omega
      step as ⟨x, hx⟩
      have hx' : (bytes xs)[(bytes other).length]? = some x.val := by
        rw [bytes_length, bytes_getElem?, List.getElem?_eq_getElem (by scalar_tac), hx]
        simp
      apply Bool.eq_iff_iff.mpr
      rw [key]
      simp only [decide_eq_true_eq, hpre, true_and, hx', Option.some.injEq]
      constructor
      · intro h; right; exact (u8_eq_47 x).mp h
      · rintro (h | h)
        · simp only [bytes_length] at h; omega
        · exact (u8_eq_47 x).mpr h
  next hbf =>
    apply (spec_ok _).mpr
    symm
    rw [Bool.eq_false_iff]
    intro h
    exact hbf (hb.mpr (key.mp h).1)

/-- The token suffix test, for a nonempty suffix, equals a byte suffix. -/
theorem tokenSuffix_iff (X O : List Nat) (hX : ValidPointer X) (hO : ValidPointer O) (hne : O ≠ []) :
    isTokenSuffix (encodedTokens O) (encodedTokens X) = true ↔ O <:+ X := by
  rw [isTokenSuffix_iff]
  have hO47 : O.head? = some 47 := by
    rcases slashLed_of_valid O hO with h | h
    · exact absurd h hne
    · exact h
  constructor
  · rintro ⟨ws, hws⟩
    refine ⟨renderEncoded ws, ?_⟩
    rw [← render_tokens_of_valid X hX, hws, renderEncoded_append, render_tokens_of_valid O hO]
  · rintro ⟨L, rfl⟩
    have hL := (valid_split L O hX (Or.inr hO47)).1
    exact ⟨encodedTokens L, encodedTokens_append L O (slashLed_of_valid L hL) (Or.inr hO47)⟩

theorem endsWithAdapted : EndsWithContract := by
  intro xs other hv ho
  apply ok_of_spec
  unfold jsonptr.adapted_api.ends_with_adapted
  step as ⟨b, hb⟩
  split
  next hxe =>
    have hx0 : bytes xs = [] := by
      have : xs.length = 0 := by simpa [hb] using hxe
      simpa [bytes] using this
    step as ⟨b1, hb1⟩
    split
    next hoe =>
      have ho0 : bytes other = [] := by
        have : other.length = 0 := by simpa [hb1] using hoe
        simpa [bytes] using this
      simp [endsWith, ho0, hx0]
    next hone =>
      have ho0 : bytes other ≠ [] := by
        intro h; apply hone; simp [hb1]; simpa [bytes] using h
      apply spec_mono (endsWithExt_spec xs other)
      intro r hr
      simp only [endsWith, ho0, ↓reduceIte]
      rw [Bool.eq_iff_iff, hr, tokenSuffix_iff _ _ hv ho ho0]
  next hxne =>
    step as ⟨b1, hb1⟩
    split
    next hoe =>
      have ho0 : bytes other = [] := by
        have : other.length = 0 := by simpa [hb1] using hoe
        simpa [bytes] using this
      have hx0 : bytes xs ≠ [] := by
        intro h; apply hxne; simp [hb]; simpa [bytes] using h
      simp [endsWith, ho0, hx0]
    next hone =>
      have ho0 : bytes other ≠ [] := by
        intro h; apply hone; simp [hb1]; simpa [bytes] using h
      apply spec_mono (endsWithExt_spec xs other)
      intro r hr
      simp only [endsWith, ho0, ↓reduceIte]
      rw [Bool.eq_iff_iff, hr, tokenSuffix_iff _ _ hv ho ho0]

/-- Behaviour of `strip_suffix_adapted` on bytes. -/
theorem stripSuffix_spec (xs suf : Slice U8) :
    jsonptr.adapted_api.strip_suffix_adapted xs suf ⦃ r =>
      obytes r = if bytes suf <:+ bytes xs then
        some ((bytes xs).take ((bytes xs).length - (bytes suf).length)) else none ⦄ := by
  unfold jsonptr.adapted_api.strip_suffix_adapted
  apply spec_bind (endsWithExt_spec xs suf)
  intro b hb
  split
  next hbt =>
    have hs : bytes suf <:+ bytes xs := hb.mp hbt
    have hl := hs.length_le
    simp only [bytes_length] at hl
    step as ⟨d, hd⟩
    step as ⟨s1, hs1, _⟩
    have hd' : d.val = (bytes xs).length - (bytes suf).length := by simp; scalar_tac
    rw [if_pos hs]
    simp only [obytes, Option.map_some, Option.some.injEq]
    rw [← hd']; simp [bytes, hs1, List.map_take]
  next hbf =>
    apply (spec_ok _).mpr
    have : ¬ bytes suf <:+ bytes xs := fun h => hbf (hb.mpr h)
    simp [obytes, this]

theorem stripSuffixAdapted : StripSuffixContract := by
  intro xs suf hv hs
  obtain ⟨r, hr, hm⟩ := ok_of_spec (stripSuffix_spec xs suf)
  have model : stripSuffix (bytes xs) (bytes suf) = if bytes suf <:+ bytes xs then
      some ((bytes xs).take ((bytes xs).length - (bytes suf).length)) else none := by
    by_cases hsn : bytes suf = []
    · simp only [stripSuffix, hsn, encodedTokens_nil, List.nil_suffix, ↓reduceIte, List.length_nil,
        Nat.sub_zero, List.take_length]
      have : isTokenSuffix [] (encodedTokens (bytes xs)) = true := by
        rw [isTokenSuffix_iff]; exact ⟨_, (List.append_nil _).symm⟩
      simp [this, render_tokens_of_valid _ hv]
    · simp only [stripSuffix]
      by_cases hsx : bytes suf <:+ bytes xs
      · have htk := (tokenSuffix_iff _ _ hv hs hsn).mpr hsx
        rw [if_pos htk, if_pos hsx]
        obtain ⟨L, hL⟩ := hsx
        have hO47 : (bytes suf).head? = some 47 := by
          rcases slashLed_of_valid _ hs with h | h
          · exact absurd h hsn
          · exact h
        have hvL := (valid_split L (bytes suf) (hL ▸ hv) (Or.inr hO47)).1
        have htok : encodedTokens (bytes xs) = encodedTokens L ++ encodedTokens (bytes suf) := by
          rw [← hL]; exact encodedTokens_append _ _ (slashLed_of_valid _ hvL) (Or.inr hO47)
        rw [htok]
        simp only [List.length_append, Nat.add_sub_cancel, List.take_left']
        rw [render_tokens_of_valid _ hvL, ← hL]
        simp
      · have htk : ¬ isTokenSuffix (encodedTokens (bytes suf)) (encodedTokens (bytes xs)) = true :=
          fun h => hsx ((tokenSuffix_iff _ _ hv hs hsn).mp h)
        rw [if_neg htk, if_neg hsx]
  refine ⟨r, hr, by rw [hm, model], ?_⟩
  intro v hvr
  rw [hm] at hvr
  split at hvr
  next hsx =>
    simp at hvr; subst hvr
    obtain ⟨L, hL⟩ := hsx
    have : (bytes xs).take ((bytes xs).length - (bytes suf).length) = L := by
      rw [← hL]; simp
    have e2 : (↑xs : List U8).length - (↑suf : List U8).length = (bytes xs).length - (bytes suf).length := by
      simp [bytes]
    rw [e2, this]
    by_cases hsn : bytes suf = []
    · rw [hsn, List.append_nil] at hL; rw [hL]; exact hv
    · have hO47 : (bytes suf).head? = some 47 := by
        rcases slashLed_of_valid _ hs with h | h
        · exact absurd h hsn
        · exact h
      exact (valid_split L (bytes suf) (hL ▸ hv) (Or.inr hO47)).1
  next => simp at hvr

/-- Behaviour of `strip_prefix_adapted` on bytes. -/
theorem stripPrefix_spec (xs pre : Slice U8) :
    jsonptr.adapted_api.strip_prefix_adapted xs pre ⦃ r =>
      obytes r = if bytes pre <+: bytes xs then some ((bytes xs).drop (bytes pre).length) else none ⦄ := by
  unfold jsonptr.adapted_api.strip_prefix_adapted
  apply spec_bind (startsWithExt_spec xs pre)
  intro b hb
  split
  next hbt =>
    have hs : bytes pre <+: bytes xs := hb.mp hbt
    have hl := hs.length_le
    simp only [bytes_length] at hl
    step as ⟨s1, hs1, _⟩
    rw [if_pos hs]
    simp only [obytes, Option.map_some, Option.some.injEq]
    simp [bytes, hs1, List.map_drop]
  next hbf =>
    apply (spec_ok _).mpr
    have : ¬ bytes pre <+: bytes xs := fun h => hbf (hb.mpr h)
    simp [obytes, this]

/-- Behaviour record: the intended `strip_prefix` contract holds whenever
`starts_with` holds. -/
theorem stripPrefixWhenStartsWith : StripPrefixWhenStartsWithRecord := by
  intro xs pre hv hp hsw
  obtain ⟨r, hr, hm⟩ := ok_of_spec (stripPrefix_spec xs pre)
  obtain ⟨R, hR, hRh⟩ := (startsWith_iff _ _ hv hp).mp hsw
  have hpre : bytes pre <+: bytes xs := ⟨R, hR.symm⟩
  have hdrop : (bytes xs).drop (bytes pre).length = R := by rw [hR]; simp
  have hvR := (valid_split (bytes pre) R (hR ▸ hv) hRh).2
  have model : stripPrefix (bytes xs) (bytes pre) = some R := by
    simp only [stripPrefix, hsw, ↓reduceIte]
    rw [hR, encodedTokens_append _ _ (slashLed_of_valid _ hp) hRh]
    simp [render_tokens_of_valid _ hvR]
  refine ⟨r, hr, by rw [hm, model, if_pos hpre, hdrop], ?_⟩
  intro v hv'
  rw [hm, if_pos hpre, hdrop] at hv'; cases hv'; exact hvR

/-! ## Intersection -/

theorem commonPrefix_eq (ts us : List (List Nat)) (k : Nat) (htake : ts.take k = us.take k)
    (hk : k ≤ ts.length) (hku : k ≤ us.length)
    (hstop : k = ts.length ∨ k = us.length ∨ ts[k]? ≠ us[k]?) :
    commonPrefix ts us = ts.take k := by
  induction k generalizing ts us with
  | zero =>
    cases ts with
    | nil => cases us <;> simp [commonPrefix]
    | cons t ts =>
      cases us with
      | nil => simp [commonPrefix]
      | cons u us =>
        simp at hstop
        simp [commonPrefix, hstop]
  | succ k ih =>
    cases ts with
    | nil => simp at hk
    | cons t ts =>
      cases us with
      | nil => simp at hku
      | cons u us =>
        simp only [List.take_succ_cons, List.cons.injEq] at htake
        obtain ⟨rfl, htake⟩ := htake
        simp only [commonPrefix, ↓reduceIte, List.take_succ_cons, List.cons.injEq, true_and]
        apply ih ts us htake (by simp at hk; omega) (by simp at hku; omega)
        simpa using hstop

theorem renderEncoded_take_succ (ts : List (List Nat)) (k : Nat) (t : List Nat) (h : ts[k]? = some t) :
    renderEncoded (ts.take (k + 1)) = renderEncoded (ts.take k) ++ 47 :: t := by
  have hk : k < ts.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.take_succ, h]
  simp [renderEncoded_append, renderEncoded]

/-- The byte result of splitting a rendered list at the end of its first `k` tokens. -/
theorem split_render_prefix (ts : List (List Nat)) (k : Nat) (hts : ∀ t ∈ ts, 47 ∉ t) :
    (match splitAtOffset (renderEncoded ts) (renderEncoded (ts.take k)).length with
      | none => renderEncoded ts
      | some p => p.1) = renderEncoded (ts.take k) := by
  have hX : renderEncoded ts = renderEncoded (ts.take k) ++ renderEncoded (ts.drop k) := by
    rw [← renderEncoded_append, List.take_append_drop]
  rcases renderEncoded_head (ts.drop k) with h | h
  · have : splitAtOffset (renderEncoded ts) (renderEncoded (ts.take k)).length = none := by
      simp only [splitAtOffset]
      rw [hX, h, List.append_nil, List.getElem?_eq_none (le_refl _)]; simp
    rw [this]; simp only; rw [hX, h, List.append_nil]
  · have hne : renderEncoded (ts.drop k) ≠ [] := by intro e; rw [e] at h; simp at h
    have h47 : (renderEncoded ts)[(renderEncoded (ts.take k)).length]? = some 47 := by
      rw [hX, head?_eq_of_append _ _ (by simp; exact List.length_pos_of_ne_nil hne)]; exact h
    simp only [splitAtOffset, h47, ↓reduceIte]
    rw [hX]; simp

theorem intersectionAdapted : IntersectionContract := by
  intro xs other hv ho
  apply ok_of_spec
  unfold jsonptr.adapted_api.intersection_adapted
  step as ⟨b, hb⟩
  split
  next hxe =>
    have hx0 : bytes xs = [] := by
      have : xs.length = 0 := by simpa [hb] using hxe
      simpa [bytes] using this
    apply (spec_ok _).mpr
    have he : bytes (Array.to_slice (Std.Array.empty U8)) = [] := by
      simp [bytes, Array.to_slice, Std.Array.empty]
    refine ⟨by rw [he]; simp [intersection, hx0, encodedTokens_nil, commonPrefix, renderEncoded], ?_⟩
    rw [ValidPtr, he]; exact (validPointer_iff []).mpr ⟨Or.inl rfl, noBad_nil⟩
  next hxne =>
    step as ⟨b1, hb1⟩
    split
    next hoe =>
      have ho0 : bytes other = [] := by
        have : other.length = 0 := by simpa [hb1] using hoe
        simpa [bytes] using this
      apply (spec_ok _).mpr
      have he : bytes (Array.to_slice (Std.Array.empty U8)) = [] := by
        simp [bytes, Array.to_slice, Std.Array.empty]
      refine ⟨by rw [he]; cases encodedTokens (bytes xs) <;> simp [intersection, ho0, encodedTokens_nil, commonPrefix, renderEncoded], ?_⟩
      rw [ValidPtr, he]; exact (validPointer_iff []).mpr ⟨Or.inl rfl, noBad_nil⟩
    next hone =>
      apply spec_bind (tokens_spec xs)
      rintro ta ⟨hpa, hinva, _⟩
      apply spec_bind (tokens_spec other)
      rintro tb ⟨hpb, hinvb, _⟩
      set ts := encodedTokens (bytes xs) with hts
      set us := encodedTokens (bytes other) with hus
      have hXr : renderEncoded ts = bytes xs := render_tokens_of_valid _ hv
      have hnos : ∀ t ∈ ts, 47 ∉ t := noSlash_tokens ts _ hts
      have hXlen : (bytes xs).length ≤ Usize.max := by simp
      -- the common exit
      have exit_val : ∀ (k : Nat) (i : Usize), i.val = (renderEncoded (ts.take k)).length →
          commonPrefix ts us = ts.take k →
          ∃ o, jsonptr.adapted_api.split_at_offset_adapted xs i = .ok o ∧
            bytes (match o with | none => xs | some p => p.1) = intersection (bytes xs) (bytes other) ∧
            ValidPtr (match o with | none => xs | some p => p.1) := by
        intro k i hi hcp
        obtain ⟨o, hos, hoe⟩ := ok_of_spec (splitAtOffset_spec xs i)
        refine ⟨o, hos, ?_⟩
        have hres := split_render_prefix ts k hnos
        rw [hXr, ← hi] at hres
        have hint : intersection (bytes xs) (bytes other) = renderEncoded (ts.take k) := by
          simp only [intersection, ← hts, ← hus, hcp]
        have hvalid : ValidPointer (renderEncoded (ts.take k)) :=
          validPointer_of_tokOK _ (fun t ht => tokOK_of_validPointer _ hv t (List.mem_of_mem_take ht))
        cases o with
        | none =>
          simp only [opbytes, Option.map_none] at hoe
          rw [← hoe] at hres; simp only at hres
          rw [hint, ← hres]; exact ⟨rfl, hv⟩
        | some p =>
          obtain ⟨s1, s2⟩ := p
          simp only [opbytes, Option.map_some] at hoe
          rw [← hoe] at hres; simp only at hres
          simp only
          rw [hint, ← hres]; exact ⟨rfl, by rw [ValidPtr, hres]; exact hvalid⟩
      unfold jsonptr.adapted_api.intersection_adapted_loop
      apply loop.spec_decr_nat
        (fun p : Usize × jsonptr.adapted_api.TokensAdapted × jsonptr.adapted_api.TokensAdapted =>
          (piecesOf p.2.1).length)
        (fun p => TokInv p.2.1 ∧ TokInv p.2.2 ∧ ∃ k, piecesOf p.2.1 = ts.drop k ∧
          piecesOf p.2.2 = us.drop k ∧ ts.take k = us.take k ∧
          p.1.val = (renderEncoded (ts.take k)).length ∧ k ≤ ts.length ∧ k ≤ us.length)
      · rintro ⟨i, a, c⟩ ⟨hia, hic, k, hpa', hpc', htk, hik, hk, hku⟩
        simp only at hia hic hpa' hpc' hik
        simp only [jsonptr.adapted_api.intersection_adapted_loop.body]
        step with tokensNext_spec a hia as ⟨o, a2, hoa, hpa2, hia2, _⟩
        cases o with
        | none =>
          have hkt : k = ts.length := by
            rw [hpa'] at hoa
            by_contra hne
            have : ts.drop k ≠ [] := by simp; omega
            cases h : ts.drop k with
            | nil => exact this h
            | cons _ _ => rw [h] at hoa; simp at hoa
          obtain ⟨o, hos, hy1, hy2⟩ := exit_val k i hik (commonPrefix_eq ts us k htk hk hku (Or.inl hkt))
          apply spec_bind (show jsonptr.adapted_api.split_at_offset_adapted xs i ⦃ fun x => x = o ⦄ by rw [hos]; exact (spec_ok _).mpr rfl)
          intro x hx; rw [hx]
          cases o with
          | none => apply (spec_ok _).mpr; exact ⟨hy1, hy2⟩
          | some p => obtain ⟨p1, p2⟩ := p; apply (spec_ok _).mpr; exact ⟨hy1, hy2⟩
        | some sa =>
          rw [hpa'] at hoa hpa2
          obtain ⟨ta1, hta1⟩ : ∃ t, ts[k]? = some t := by
            cases h : ts[k]? with
            | none => rw [List.head?_drop, h] at hoa; simp at hoa
            | some t => exact ⟨t, rfl⟩
          rw [List.head?_drop, hta1] at hoa
          simp only [Option.map_some, Option.some.injEq] at hoa
          step with tokensNext_spec c hic as ⟨o2, c2, hoc, hpc2, hic2, _⟩
          cases o2 with
          | none =>
            have hku' : k = us.length := by
              rw [hpc'] at hoc
              by_contra hne
              have : us.drop k ≠ [] := by simp; omega
              cases h : us.drop k with
              | nil => exact this h
              | cons _ _ => rw [h] at hoc; simp at hoc
            obtain ⟨o, hos, hy1, hy2⟩ := exit_val k i hik (commonPrefix_eq ts us k htk hk hku (Or.inr (Or.inl hku')))
            apply spec_bind (show jsonptr.adapted_api.split_at_offset_adapted xs i ⦃ fun x => x = o ⦄ by rw [hos]; exact (spec_ok _).mpr rfl)
            intro x hx; rw [hx]
            cases o with
            | none => apply (spec_ok _).mpr; exact ⟨hy1, hy2⟩
            | some p => obtain ⟨p1, p2⟩ := p; apply (spec_ok _).mpr; exact ⟨hy1, hy2⟩
          | some sc =>
            rw [hpc'] at hoc hpc2
            obtain ⟨tc1, htc1⟩ : ∃ t, us[k]? = some t := by
              cases h : us[k]? with
              | none => rw [List.head?_drop, h] at hoc; simp at hoc
              | some t => exact ⟨t, rfl⟩
            rw [List.head?_drop, htc1] at hoc
            simp only [Option.map_some, Option.some.injEq] at hoc
            apply spec_bind (bytesEq_spec sa sc)
            intro beq hbeq
            split
            next hbt =>
              have heq : ta1 = tc1 := by rw [← hoa, ← hoc]; exact hbeq.mp hbt
              have hk1 : k < ts.length := (List.getElem?_eq_some_iff.mp hta1).1
              have hlenr := renderEncoded_take_succ ts k ta1 hta1
              have hle : (renderEncoded (ts.take (k + 1))).length ≤ (bytes xs).length := by
                rw [← hXr]
                conv_rhs => rw [← List.take_append_drop (k + 1) ts, renderEncoded_append]
                simp
              have hsa : sa.length = ta1.length := by rw [← hoa]; simp
              step as ⟨l1, hl1⟩
              have hb2 : i.val + l1.val ≤ Usize.max := by
                rw [hlenr] at hle; simp at hle; scalar_tac
              step as ⟨i3, hi3⟩
              have hpu1 : k + 1 ≤ us.length := (List.getElem?_eq_some_iff.mp htc1).1
              have hA : piecesOf a2 = ts.drop (k + 1) := by rw [hpa2, List.tail_drop]
              have hB : piecesOf c2 = us.drop (k + 1) := by rw [hpc2, List.tail_drop]
              have hC : ts.take (k + 1) = us.take (k + 1) := by
                rw [List.take_succ, List.take_succ, htk, hta1, htc1, heq]
              have hD : i3.val = (renderEncoded (ts.take (k + 1))).length := by
                rw [hlenr]; simp; scalar_tac
              have hE : (piecesOf a2).length < (piecesOf a).length := by
                rw [hpa2, hpa']; simp; omega
              exact ⟨hia2, hic2, ⟨k + 1, hA, hB, hC, hD, hk1, hpu1⟩, hE⟩
            next hbf =>
              have hne : ts[k]? ≠ us[k]? := by
                rw [hta1, htc1]; intro e; apply hbf; simp at e
                exact hbeq.mpr (by rw [hoa, hoc, e])
              obtain ⟨o, hos, hy1, hy2⟩ := exit_val k i hik (commonPrefix_eq ts us k htk hk hku (Or.inr (Or.inr hne)))
              apply spec_bind (show jsonptr.adapted_api.split_at_offset_adapted xs i ⦃ fun x => x = o ⦄ by rw [hos]; exact (spec_ok _).mpr rfl)
              intro x hx; rw [hx]
              cases o with
              | none => apply (spec_ok _).mpr; exact ⟨hy1, hy2⟩
              | some p => obtain ⟨p1, p2⟩ := p; apply (spec_ok _).mpr; exact ⟨hy1, hy2⟩
      · refine ⟨hinva, hinvb, 0, by simp [hpa], by simp [hpb], by simp, by simp [renderEncoded], by simp, by simp⟩

end JsonptrExtProofs
