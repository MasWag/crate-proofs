import ExtProofs.Tokens

/-!
# Specs of the byte helpers and further model lemmas (implementation agent)
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem bytes_getElem? (s : Slice U8) (k : Nat) :
    (bytes s)[k]? = (s.val[k]?).map (fun b => b.val) := by
  simp [bytes, List.getElem?_map]

theorem u8_eq_47 (x : U8) : x = 47#u8 ↔ x.val = 47 := by
  constructor
  · intro h; subst h; rfl
  · intro h; exact UScalar.eq_of_val_eq (by simpa using h)

/-- First-slash postcondition. -/
def SlashFirst (l : List Nat) (len : Nat) : Option Usize → Prop
  | none => 47 ∉ l
  | some j => j.val < len ∧ l[j.val]? = some 47 ∧ ∀ k, k < j.val → l[k]? ≠ some 47

/-- Last-slash postcondition. -/
def SlashLast (l : List Nat) (len : Nat) : Option Usize → Prop
  | none => 47 ∉ l
  | some i => i.val < len ∧ l[i.val]? = some 47 ∧ ∀ k, i.val < k → l[k]? ≠ some 47

/-- `find_slash_adapted` (phase-1 helper) finds the first slash. -/
theorem findSlash_spec (s : Slice U8) :
    jsonptr.pointer.find_slash_adapted s ⦃ SlashFirst (bytes s) s.length ⦄ := by
  unfold jsonptr.pointer.find_slash_adapted jsonptr.pointer.find_slash_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ k, k < i.val → (bytes s)[k]? ≠ some 47)
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.pointer.find_slash_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi)
      intro x hx
      have hx' : (bytes s)[i.val]? = some x.val := by
        rw [bytes_getElem?, List.getElem?_eq_getElem hi, hx]; rfl
      split
      next heq =>
        apply (spec_ok _).mpr
        exact ⟨hi, by rw [hx', (u8_eq_47 x).mp heq], hall⟩
      next hne =>
        step as ⟨i', hi'⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk
        by_cases hki : k < i.val
        · exact hall k hki
        · have : k = i.val := by scalar_tac
          subst this; rw [hx']; intro e; apply hne; simp at e; exact (u8_eq_47 x).mpr e
    next hge =>
      apply (spec_ok _).mpr
      intro hm
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
      have : k < s.length := by simpa using (List.getElem?_eq_some_iff.mp hk).1
      exact hall k (by scalar_tac) hk
  · exact ⟨by scalar_tac, fun k hk => by scalar_tac⟩

/-- `rfind_slash_ext` finds the last slash. -/
theorem rfindSlash_spec (s : Slice U8) :
    jsonptr.adapted_api.rfind_slash_ext s ⦃ SlashLast (bytes s) s.length ⦄ := by
  simp only [jsonptr.adapted_api.rfind_slash_ext]
  unfold jsonptr.adapted_api.rfind_slash_ext_loop
  apply loop.spec_decr_nat (fun i : Usize => i.val)
    (fun i => i.val ≤ s.length ∧ ∀ k, i.val ≤ k → (bytes s)[k]? ≠ some 47)
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.adapted_api.rfind_slash_ext_loop.body]
    split
    next hpos =>
      step as ⟨i1, hi1⟩
      have hi : i1.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i1 hi)
      intro x hx
      have hx' : (bytes s)[i1.val]? = some x.val := by
        rw [bytes_getElem?, List.getElem?_eq_getElem hi, hx]; rfl
      split
      next heq =>
        apply (spec_ok _).mpr
        exact ⟨hi, by rw [hx', (u8_eq_47 x).mp heq], fun k hk => hall k (by scalar_tac)⟩
      next hne =>
        apply (spec_ok _).mpr
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k hk
        by_cases hki : i.val ≤ k
        · exact hall k hki
        · have : k = i1.val := by scalar_tac
          subst this; rw [hx']; intro e; apply hne; simp at e; exact (u8_eq_47 x).mpr e
    next hz =>
      apply (spec_ok _).mpr
      intro hm
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
      exact hall k (by scalar_tac) hk
  · refine ⟨by scalar_tac, fun k hk => ?_⟩
    have : s.length ≤ k := by scalar_tac
    rw [List.getElem?_eq_none (by simpa using this)]; simp

/-- `bytes_eq_ext` decides byte equality. -/
theorem bytesEq_spec (a b : Slice U8) :
    jsonptr.adapted_api.bytes_eq_ext a b ⦃ r => (r = true ↔ bytes a = bytes b) ⦄ := by
  simp only [jsonptr.adapted_api.bytes_eq_ext]
  split
  next hne =>
    apply (spec_ok _).mpr
    constructor
    · intro h; cases h
    · intro h
      have := congrArg List.length h
      simp at this
      have hne' : a.len ≠ b.len := by simpa using hne
      exact absurd (by scalar_tac) hne'
  next heq =>
    have hlen : a.length = b.length := by scalar_tac
    unfold jsonptr.adapted_api.bytes_eq_ext_loop
    apply loop.spec_decr_nat (fun i : Usize => a.length - i.val)
      (fun i => i.val ≤ a.length ∧ ∀ k, k < i.val → (bytes a)[k]? = (bytes b)[k]?)
    · rintro i ⟨hle, hall⟩
      simp only [jsonptr.adapted_api.bytes_eq_ext_loop.body]
      split
      next hlt =>
        have hi : i.val < a.length := by scalar_tac
        have hib : i.val < b.length := by scalar_tac
        apply spec_bind (Slice.index_usize_spec a i hi)
        intro x hx
        apply spec_bind (Slice.index_usize_spec b i hib)
        intro y hy
        split
        next hxy =>
          apply (spec_ok _).mpr
          constructor
          · intro h; cases h
          · intro h
            have := congrArg (fun l => l[i.val]?) h
            simp only [bytes_getElem?, List.getElem?_eq_getElem hi,
              List.getElem?_eq_getElem hib] at this
            simp at this
            have hxy' : x ≠ y := by simpa using hxy
            exact absurd (by rw [hx, hy]; exact UScalar.eq_of_val_eq this) hxy'
        next hxy =>
          step as ⟨i4, hi4⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro k hk
          by_cases hki : k < i.val
          · exact hall k hki
          · have : k = i.val := by scalar_tac
            subst this
            simp only [bytes_getElem?, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hib]
            simp at hxy; simp [← hx, ← hy, hxy]
      next hge =>
        apply (spec_ok _).mpr
        simp only [true_iff]
        apply List.ext_getElem?
        intro k
        by_cases hk : k < a.length
        · exact hall k (by scalar_tac)
        · rw [List.getElem?_eq_none (by simp; scalar_tac), List.getElem?_eq_none (by simp; scalar_tac)]
    · exact ⟨by scalar_tac, fun k hk => by scalar_tac⟩

theorem startsWithExt_spec (h n : Slice U8) :
    jsonptr.adapted_api.str_starts_with_ext h n ⦃ r => (r = true ↔ bytes n <+: bytes h) ⦄ := by
  simp only [jsonptr.adapted_api.str_starts_with_ext]
  split
  next hge =>
    step as ⟨s, hs, _⟩
    apply spec_mono (bytesEq_spec n s)
    intro r hr
    rw [hr]
    have hb : bytes s = (bytes h).take n.length := by simp [bytes, hs, List.map_take]
    rw [hb]
    constructor
    · intro e; rw [e]; exact List.take_prefix _ _
    · intro hp
      obtain ⟨t, ht⟩ := hp
      rw [← ht]; simp
  next hlt =>
    apply (spec_ok _).mpr
    constructor
    · intro e; cases e
    · intro hp
      have := hp.length_le
      simp at this
      exact absurd (by scalar_tac) hlt

theorem endsWithExt_spec (h n : Slice U8) :
    jsonptr.adapted_api.str_ends_with_ext h n ⦃ r => (r = true ↔ bytes n <:+ bytes h) ⦄ := by
  simp only [jsonptr.adapted_api.str_ends_with_ext]
  split
  next hge =>
    step as ⟨d, hd⟩
    step as ⟨s, hs, _⟩
    apply spec_mono (bytesEq_spec n s)
    intro r hr
    rw [hr]
    have hd' : d.val = h.length - n.length := by scalar_tac
    have hb : bytes s = (bytes h).drop (h.length - n.length) := by
      rw [← hd']; simp [bytes, hs, List.map_drop]
    rw [hb]
    constructor
    · intro e; rw [e]; exact List.drop_suffix _ _
    · intro hp
      obtain ⟨t, ht⟩ := hp
      rw [← ht]
      have : t.length = h.length - n.length := by
        have := congrArg List.length ht
        simp only [List.length_append, bytes_length] at this; omega
      simp [← this]
  next hlt =>
    apply (spec_ok _).mpr
    constructor
    · intro e; cases e
    · intro hp
      have := hp.length_le
      simp at this
      exact absurd (by scalar_tac) hlt

/-! ## More model lemmas -/

theorem slashLed_of_valid (xs : List Nat) (h : ValidPointer xs) : xs = [] ∨ xs.head? = some 47 :=
  ((validPointer_iff xs).mp h).1

/-- Splitting a valid pointer before a slash gives two valid pointers. -/
theorem valid_split (A B : List Nat) (h : ValidPointer (A ++ B)) (hB : B = [] ∨ B.head? = some 47) :
    ValidPointer A ∧ ValidPointer B := by
  obtain ⟨h1, h2⟩ := (validPointer_iff _).mp h
  obtain ⟨hA, hB'⟩ := (noBad_append A B hB).mp h2
  refine ⟨(validPointer_iff A).mpr ⟨?_, hA⟩, (validPointer_iff B).mpr ⟨hB, hB'⟩⟩
  cases A with
  | nil => left; rfl
  | cons a A => right; simpa using h1

theorem encodedTokens_append (A B : List Nat) (hA : A = [] ∨ A.head? = some 47)
    (hB : B = [] ∨ B.head? = some 47) :
    encodedTokens (A ++ B) = encodedTokens A ++ encodedTokens B := by
  conv_lhs => rw [← renderEncoded_encodedTokens A hA, ← renderEncoded_encodedTokens B hB,
    ← renderEncoded_append]
  rw [encodedTokens_renderEncoded]
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact mem_encodedTokens_noSlash _ _ h
  · exact mem_encodedTokens_noSlash _ _ h

theorem isTokenPrefix_iff (us ts : List (List Nat)) : isTokenPrefix us ts = true ↔ ∃ vs, ts = us ++ vs := by
  induction us generalizing ts with
  | nil => simp [isTokenPrefix]
  | cons u us ih =>
    cases ts with
    | nil => simp [isTokenPrefix]
    | cons t ts =>
      simp only [isTokenPrefix, Bool.and_eq_true, decide_eq_true_eq, ih, List.cons_append,
        List.cons.injEq]
      constructor
      · rintro ⟨rfl, vs, rfl⟩; exact ⟨vs, rfl, rfl⟩
      · rintro ⟨vs, rfl, rfl⟩; exact ⟨rfl, vs, rfl⟩

theorem isTokenSuffix_iff (ss ts : List (List Nat)) : isTokenSuffix ss ts = true ↔ ∃ ws, ts = ws ++ ss := by
  unfold isTokenSuffix
  rw [isTokenPrefix_iff]
  constructor
  · rintro ⟨vs, h⟩
    refine ⟨vs.reverse, ?_⟩
    have := congrArg List.reverse h
    simpa using this
  · rintro ⟨ws, rfl⟩
    exact ⟨ws.reverse, by simp⟩

theorem render_tokens_of_valid (xs : List Nat) (h : ValidPointer xs) :
    renderEncoded (encodedTokens xs) = xs := renderEncoded_encodedTokens xs (slashLed_of_valid xs h)

theorem noSlash_tokens (ts : List (List Nat)) (xs : List Nat) (h : ts = encodedTokens xs) :
    ∀ t ∈ ts, 47 ∉ t := fun t ht => mem_encodedTokens_noSlash xs t (h ▸ ht)

end JsonptrExtProofs
