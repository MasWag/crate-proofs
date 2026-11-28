import SpecModelExt

/-!
# Model lemmas for the extended scope (implementation agent)

Pure facts about the specification model: splitting at slashes, rendering
token lists, the pointer and token invariants. No generated code.
-/

namespace JsonptrSpecModel.Ext

open JsonptrSpecModel

/-! ## Splitting -/

theorem splitSlash_ne_nil (l : List Nat) : splitSlash l ≠ [] := by
  cases l with
  | nil => simp [splitSlash]
  | cons b rest =>
    simp only [splitSlash]
    split
    · simp
    · split <;> simp

theorem splitSlash_noSlash (b : List Nat) (h : 47 ∉ b) : splitSlash b = [b] := by
  induction b with
  | nil => rfl
  | cons x r ih =>
    have hx : x ≠ 47 := fun e => h (e ▸ List.mem_cons_self)
    have hr : 47 ∉ r := fun m => h (List.mem_cons_of_mem _ m)
    simp [splitSlash, hx, ih hr]

theorem splitSlash_append_slash (a b : List Nat) :
    splitSlash (a ++ 47 :: b) = splitSlash a ++ splitSlash b := by
  induction a with
  | nil => simp [splitSlash]
  | cons x a ih =>
    by_cases hx : x = 47
    · subst hx; simp [splitSlash, ih]
    · obtain ⟨q, qs, hq⟩ : ∃ q qs, splitSlash a = q :: qs := by
        cases h : splitSlash a with
        | nil => exact absurd h (splitSlash_ne_nil a)
        | cons q qs => exact ⟨q, qs, rfl⟩
      simp [splitSlash, hx, ih, hq]

theorem encodedTokens_nil : encodedTokens [] = [] := rfl

theorem encodedTokens_slash (r : List Nat) : encodedTokens (47 :: r) = splitSlash r := by
  simp [encodedTokens, splitSlash]

theorem encodedTokens_cons_split (tok rem : List Nat) (ht : 47 ∉ tok)
    (hr : rem = [] ∨ rem.head? = some 47) :
    encodedTokens (47 :: (tok ++ rem)) = tok :: encodedTokens rem := by
  rw [encodedTokens_slash]
  rcases hr with h | h
  · subst h; simp [splitSlash_noSlash tok ht, encodedTokens_nil]
  · obtain ⟨r, rfl⟩ : ∃ r, rem = 47 :: r := by
      cases rem with
      | nil => simp at h
      | cons x r => simp at h; exact ⟨r, by rw [h]⟩
    rw [splitSlash_append_slash, splitSlash_noSlash tok ht, encodedTokens_slash]
    rfl

/-- Splitting at the last slash. -/
theorem encodedTokens_last (a b : List Nat) (hb : 47 ∉ b) (ha : a = [] ∨ a.head? = some 47) :
    encodedTokens (a ++ 47 :: b) = encodedTokens a ++ [b] := by
  rcases ha with h | h
  · subst h; simp [encodedTokens_slash, splitSlash_noSlash b hb, encodedTokens_nil]
  · obtain ⟨r, rfl⟩ : ∃ r, a = 47 :: r := by
      cases a with
      | nil => simp at h
      | cons x r => simp at h; exact ⟨r, by rw [h]⟩
    simp only [List.cons_append, encodedTokens_slash]
    rw [splitSlash_append_slash, splitSlash_noSlash b hb]

theorem mem_splitSlash_noSlash (l t : List Nat) (h : t ∈ splitSlash l) : 47 ∉ t := by
  induction l generalizing t with
  | nil => simp [splitSlash] at h; subst h; simp
  | cons x r ih =>
    simp only [splitSlash] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp
      · exact ih t h
    · next hx =>
      split at h
      · next heq => exact absurd heq (splitSlash_ne_nil r)
      · next p ps heq =>
        rcases List.mem_cons.mp h with h | h
        · subst h
          have := ih p (by rw [heq]; exact List.mem_cons_self)
          simp only [List.mem_cons, not_or]; exact ⟨fun e => hx e.symm, this⟩
        · exact ih t (by rw [heq]; exact List.mem_cons_of_mem _ h)

theorem mem_encodedTokens_noSlash (xs t : List Nat) (h : t ∈ encodedTokens xs) : 47 ∉ t :=
  mem_splitSlash_noSlash xs t (List.mem_of_mem_drop h)

/-! ## Rendering -/

theorem renderEncoded_append (a b : List (List Nat)) :
    renderEncoded (a ++ b) = renderEncoded a ++ renderEncoded b := by
  induction a with
  | nil => rfl
  | cons t ts ih => simp [renderEncoded, ih]

theorem renderEncoded_head (ts : List (List Nat)) :
    renderEncoded ts = [] ∨ (renderEncoded ts).head? = some 47 := by
  cases ts with
  | nil => left; rfl
  | cons t ts => right; simp [renderEncoded]

theorem encodedTokens_renderEncoded (ts : List (List Nat)) (h : ∀ t ∈ ts, 47 ∉ t) :
    encodedTokens (renderEncoded ts) = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [renderEncoded]
    rw [encodedTokens_cons_split t _ (h t List.mem_cons_self) (renderEncoded_head ts),
      ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

theorem renderEncoded_splitSlash (r : List Nat) : renderEncoded (splitSlash r) = 47 :: r := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    by_cases hx : x = 47
    · subst hx; simp [splitSlash, renderEncoded, ih]
    · obtain ⟨p, ps, hp⟩ : ∃ p ps, splitSlash r = p :: ps := by
        cases h : splitSlash r with
        | nil => exact absurd h (splitSlash_ne_nil r)
        | cons p ps => exact ⟨p, ps, rfl⟩
      rw [hp] at ih
      simp only [renderEncoded, List.cons.injEq, true_and] at ih
      simp [splitSlash, hx, hp, renderEncoded, ih]

/-- Rendering the tokens of a slash-led byte list gives it back. -/
theorem renderEncoded_encodedTokens (xs : List Nat) (h : xs = [] ∨ xs.head? = some 47) :
    renderEncoded (encodedTokens xs) = xs := by
  rcases h with h | h
  · subst h; rfl
  · obtain ⟨r, rfl⟩ : ∃ r, xs = 47 :: r := by
      cases xs with
      | nil => simp at h
      | cons x r => simp at h; exact ⟨r, by rw [h]⟩
    rw [encodedTokens_slash, renderEncoded_splitSlash]

/-! ## The escape invariant -/

/-- No bad escape anywhere. -/
def NoBad (l : List Nat) : Prop := ∀ j, ¬ BadEscape l j

/-- An encoded token as a pointer contains it: no slash, no bad escape. -/
def TokOK (t : List Nat) : Prop := 47 ∉ t ∧ NoBad t

theorem noBad_nil : NoBad [] := by
  intro j h; simp [BadEscape] at h

theorem noBad_cons (b : Nat) (r : List Nat) :
    NoBad (b :: r) ↔ (b = 126 → r.head? = some 48 ∨ r.head? = some 49) ∧ NoBad r := by
  constructor
  · intro h
    refine ⟨fun hb => ?_, fun j hj => h (j + 1) (by simpa [BadEscape] using hj)⟩
    cases r with
    | nil => exact absurd (⟨by simp [hb], by simp, by simp⟩ : BadEscape [b] 0) (h 0)
    | cons c r' =>
      by_cases c48 : c = 48
      · left; simp [c48]
      · by_cases c49 : c = 49
        · right; simp [c49]
        · exact absurd (⟨by simp [hb], by simp [c48], by simp [c49]⟩ : BadEscape (b :: c :: r') 0) (h 0)
  · rintro ⟨h1, h2⟩ j ⟨hj1, hj2, hj3⟩
    cases j with
    | zero =>
      simp at hj1
      rcases h1 hj1 with h | h <;> cases r <;> simp_all
    | succ j => exact h2 j ⟨by simpa using hj1, by simpa using hj2, by simpa using hj3⟩

theorem noBad_append (t R : List Nat) (hR : R = [] ∨ R.head? = some 47) :
    NoBad (t ++ R) ↔ NoBad t ∧ NoBad R := by
  induction t with
  | nil => simp [noBad_nil]
  | cons b t ih =>
    rw [List.cons_append, noBad_cons, noBad_cons, ih]
    cases t with
    | nil =>
      simp only [List.nil_append, List.head?_nil, reduceCtorEq, or_self]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨fun hb => ?_, h2⟩, h3⟩
        rcases hR with hR | hR
        · subst hR; simpa using h1 hb
        · rcases h1 hb with h | h <;> simp_all
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨fun hb => absurd (h1 hb) id, h2, h3⟩
    | cons c t =>
      simp only [List.cons_append, List.head?_cons]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

theorem validPointer_iff (xs : List Nat) :
    ValidPointer xs ↔ (xs = [] ∨ xs.head? = some 47) ∧ NoBad xs := by
  unfold ValidPointer NoBad
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · right; cases xs <;> simp_all
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · exact Or.inl h
    · right; cases xs <;> simp_all

theorem validPointer_renderEncoded (ts : List (List Nat)) :
    ValidPointer (renderEncoded ts) ↔ ∀ t ∈ ts, NoBad t := by
  rw [validPointer_iff]
  induction ts with
  | nil => simp [renderEncoded, noBad_nil]
  | cons t ts ih =>
    simp only [renderEncoded, List.mem_cons, forall_eq_or_imp]
    rw [noBad_cons, noBad_append t _ (renderEncoded_head ts), ← ih]
    simp only [List.head?_cons, reduceCtorEq, or_true, true_and]
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, renderEncoded_head ts, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨by intro h; omega, h1, h2⟩

/-- The tokens of a valid pointer satisfy the token invariant. -/
theorem tokOK_of_validPointer (xs : List Nat) (hv : ValidPointer xs) :
    ∀ t ∈ encodedTokens xs, TokOK t := by
  have hhead := ((validPointer_iff xs).mp hv).1
  have hr : ValidPointer (renderEncoded (encodedTokens xs)) := by
    rw [renderEncoded_encodedTokens xs hhead]; exact hv
  intro t ht
  exact ⟨mem_encodedTokens_noSlash xs t ht, (validPointer_renderEncoded _).mp hr t ht⟩

theorem validPointer_of_tokOK (ts : List (List Nat)) (h : ∀ t ∈ ts, TokOK t) :
    ValidPointer (renderEncoded ts) :=
  (validPointer_renderEncoded ts).mpr (fun t ht => (h t ht).2)

/-- The token invariant implies the image-of-`E` invariant. -/
theorem validEncodedToken_of_tokOK (t : List Nat) (h : TokOK t) : ValidEncodedToken t := by
  obtain ⟨hs, hb⟩ := h
  suffices H : ∀ n (t : List Nat), t.length ≤ n → 47 ∉ t → NoBad t → ∃ x, encode x = t from
    H t.length t (Nat.le_refl _) hs hb
  intro n
  induction n with
  | zero =>
    intro t ht _ _
    exact ⟨[], by simp [List.length_eq_zero_iff.mp (Nat.le_zero.mp ht), encode]⟩
  | succ n ih =>
    intro t ht hs hb
    cases t with
    | nil => exact ⟨[], rfl⟩
    | cons b r =>
      have hb47 : b ≠ 47 := fun e => hs (e ▸ List.mem_cons_self)
      have hr47 : 47 ∉ r := fun m => hs (List.mem_cons_of_mem _ m)
      obtain ⟨h1, h2⟩ := (noBad_cons b r).mp hb
      by_cases h126 : b = 126
      · subst h126
        obtain ⟨c, r', rfl⟩ : ∃ c r', r = c :: r' := by
          cases r with
          | nil => rcases h1 rfl with h | h <;> simp at h
          | cons c r' => exact ⟨c, r', rfl⟩
        have hc : c = 48 ∨ c = 49 := by rcases h1 rfl with h | h <;> simp_all
        have h2' := ((noBad_cons c r').mp h2).2
        obtain ⟨x, hx⟩ := ih r' (by simp at ht; omega)
          (fun m => hr47 (List.mem_cons_of_mem _ m)) h2'
        rcases hc with hc | hc
        · exact ⟨126 :: x, by subst hc; simp [encode, encodeByte, hx]⟩
        · exact ⟨47 :: x, by subst hc; simp [encode, encodeByte, hx]⟩
      · obtain ⟨x, hx⟩ := ih r (by simp at ht; omega) hr47 h2
        exact ⟨b :: x, by simp [encode, encodeByte, hb47, h126, hx]⟩

theorem validEncodedToken_of_valid_mem (xs t : List Nat) (hv : ValidPointer xs)
    (ht : t ∈ encodedTokens xs) : ValidEncodedToken t :=
  validEncodedToken_of_tokOK t (tokOK_of_validPointer xs hv t ht)

end JsonptrSpecModel.Ext
