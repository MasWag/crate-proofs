import SpecModel

/-! Model-only lemmas about the specification functions (no generated code). -/

open JsonptrSpecModel

namespace JsonptrAdaptedProofs.Model

theorem splitSlash_ne_nil (l : List Nat) : ∃ h tl, splitSlash l = h :: tl := by
  cases l with
  | nil => exact ⟨[], [], rfl⟩
  | cons b rest =>
    obtain ⟨h, tl, e⟩ := splitSlash_ne_nil rest
    by_cases hb : b = 47
    · exact ⟨[], splitSlash rest, by simp [splitSlash, hb]⟩
    · exact ⟨b :: h, tl, by simp [splitSlash, hb, e]⟩

theorem splitSlash_append (t rem : List Nat) (ht : 47 ∉ t) (h : List Nat) (tl : List (List Nat))
    (e : splitSlash rem = h :: tl) : splitSlash (t ++ rem) = (t ++ h) :: tl := by
  induction t with
  | nil => simpa using e
  | cons b t ih =>
    have hb : b ≠ 47 := fun hb => ht (by simp [hb])
    have ht' : 47 ∉ t := fun hm => ht (by simp [hm])
    simp [splitSlash, hb, ih ht']

/-- Splitting `47 :: tok ++ rem` at its first token. -/
theorem encodedTokens_cons (tok rem : List Nat) (ht : 47 ∉ tok)
    (hrem : rem = [] ∨ rem.head? = some 47) :
    tok :: encodedTokens rem = encodedTokens (47 :: (tok ++ rem)) := by
  rcases hrem with rfl | hrem
  · have := splitSlash_append tok [] ht [] [] rfl
    simp only [List.append_nil] at this
    simp [encodedTokens, splitSlash, this]
  · obtain ⟨r, rfl⟩ : ∃ r, rem = 47 :: r := by
      cases rem with
      | nil => simp at hrem
      | cons a r => simp at hrem; exact ⟨r, by simp [hrem]⟩
    have := splitSlash_append tok (47 :: r) ht [] (splitSlash r) (by simp [splitSlash])
    simp [encodedTokens, splitSlash, this]

theorem drop_cons {l : List Nat} {i : Nat} {x : Nat} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.drop_eq_getElem_cons hi

/-! ### `firstEncErrorFrom` one step at a time -/

theorem fe_end (l : List Nat) : firstEncErrorFrom l.length (l.drop l.length) = none := by
  simp [firstEncErrorFrom]

theorem fe_slash {l : List Nat} {i : Nat} (h : l[i]? = some 47) :
    firstEncErrorFrom i (l.drop i) = some ⟨i, .slash⟩ := by
  rw [drop_cons h, firstEncErrorFrom.eq_def]; simp

theorem fe_other {l : List Nat} {i x : Nat} (h : l[i]? = some x) (h1 : x ≠ 47) (h2 : x ≠ 126) :
    firstEncErrorFrom i (l.drop i) = firstEncErrorFrom (i + 1) (l.drop (i + 1)) := by
  rw [drop_cons h, firstEncErrorFrom.eq_def]; simp [h1, h2]

theorem fe_esc_end {l : List Nat} {j : Nat} (h : l[j]? = some 126) (hl : l.length = j + 1) :
    firstEncErrorFrom j (l.drop j) = some ⟨j + 1, .tilde⟩ := by
  rw [drop_cons h, firstEncErrorFrom.eq_def]; simp
  have : l.drop (j + 1) = [] := by simp [hl]
  simp [firstEncErrorFrom, this]

theorem fe_esc {l : List Nat} {j c : Nat} (h : l[j]? = some 126) (hc : l[j + 1]? = some c) :
    firstEncErrorFrom j (l.drop j) =
      if c = 48 ∨ c = 49 then firstEncErrorFrom (j + 2) (l.drop (j + 2))
      else if c = 47 then some ⟨j + 1, .slash⟩ else some ⟨j + 1, .tilde⟩ := by
  rw [drop_cons h, drop_cons hc]
  simp only [firstEncErrorFrom]
  simp

/-! ### `ptrScan` one step at a time -/

theorem ps_end (l : List Nat) (sep : Nat) : ptrScan l.length sep (l.drop l.length) = none := by
  simp [ptrScan]

theorem ps_slash {l : List Nat} {p : Nat} (sep : Nat) (h : l[p]? = some 47) :
    ptrScan p sep (l.drop p) = ptrScan (p + 1) p (l.drop (p + 1)) := by
  rw [drop_cons h, ptrScan.eq_def]; simp

theorem ps_other {l : List Nat} {p x : Nat} (sep : Nat) (h : l[p]? = some x) (h1 : x ≠ 47)
    (h2 : x ≠ 126) : ptrScan p sep (l.drop p) = ptrScan (p + 1) sep (l.drop (p + 1)) := by
  rw [drop_cons h, ptrScan.eq_def]; simp [h1, h2]

theorem ps_tilde_end {l : List Nat} {p : Nat} (sep : Nat) (h : l[p]? = some 126)
    (hl : l.length = p + 1) : ptrScan p sep (l.drop p) = some (.invalidEncoding sep (p - sep)) := by
  rw [drop_cons h]
  have : l.drop (p + 1) = [] := by simp [hl]
  rw [this, ptrScan.eq_def]; simp

theorem ps_tilde {l : List Nat} {p c : Nat} (sep : Nat) (h : l[p]? = some 126)
    (hc : l[p + 1]? = some c) :
    ptrScan p sep (l.drop p) =
      if c = 48 ∨ c = 49 then ptrScan (p + 2) sep (l.drop (p + 2))
      else some (.invalidEncoding sep (p - sep)) := by
  rw [drop_cons h, drop_cons hc, ptrScan.eq_def]; simp

/-! ### Decimal values -/

theorem decimalValue_append (l : List Nat) (d : Nat) :
    decimalValue (l ++ [d]) = 10 * decimalValue l + (d - 48) := by
  simp [decimalValue, List.foldl_append]

theorem decimalValue_take_succ (l : List Nat) (i : Nat) (h : i < l.length) :
    decimalValue (l.take (i + 1)) = 10 * decimalValue (l.take i) + (l[i] - 48) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, decimalValue_append]

theorem decimalValue_take_mono (l : List Nat) (i j : Nat) (hij : i ≤ j) :
    decimalValue (l.take i) ≤ decimalValue (l.take j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have ih := ih (by omega)
    have e : i + (d + 1) = (i + d) + 1 := by omega
    rw [e]
    generalize i + d = j at ih ⊢
    by_cases hj : j < l.length
    · rw [decimalValue_take_succ l j hj]; omega
    · have e1 : l.take (j + 1) = l := List.take_of_length_le (by omega)
      have e2 : l.take j = l := List.take_of_length_le (by omega)
      rw [e1]; rw [e2] at ih; exact ih

theorem firstNonDigitFrom_none (l : List Nat) (pos : Nat) (h : ∀ b ∈ l, isDigit b = true) :
    firstNonDigitFrom pos l = none := by
  induction l generalizing pos with
  | nil => rfl
  | cons b l ih =>
    simp only [firstNonDigitFrom, h b (by simp), if_true]
    exact ih _ (fun c hc => h c (by simp [hc]))

theorem firstNonDigitFrom_some (l : List Nat) (pos j : Nat) (hj : j < l.length)
    (hbad : isDigit l[j] = false) (hpre : ∀ k (hk : k < j), isDigit (l[k]'(by omega)) = true) :
    firstNonDigitFrom pos l = some (pos + j) := by
  induction l generalizing pos j with
  | nil => simp at hj
  | cons b l ih =>
    cases j with
    | zero => simp at hbad; simp [firstNonDigitFrom, hbad]
    | succ j =>
      have hb : isDigit b = true := hpre 0 (by omega)
      simp only [firstNonDigitFrom, hb, if_true]
      rw [ih (pos + 1) j (by simpa using hj) (by simpa using hbad)
        (fun k hk => by simpa using hpre (k + 1) (by omega))]
      congr 1; omega

/-! ### Encoding -/

theorem encode_append (a b : List Nat) : encode (a ++ b) = encode a ++ encode b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [encode, ih]

theorem encode_take_succ (l : List Nat) (k : Nat) (h : k < l.length) :
    encode (l.take (k + 1)) = encode (l.take k) ++ encodeByte l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, encode_append]
  simp [encode]

theorem encodeByte_length (b : Nat) : (encodeByte b).length ≤ 2 := by
  unfold encodeByte
  split
  · simp
  · split <;> simp

theorem encode_length_le (l : List Nat) : (encode l).length ≤ 2 * l.length := by
  induction l with
  | nil => simp [encode]
  | cons x l ih => have := encodeByte_length x; simp [encode]; omega

theorem encode_eq_self (l : List Nat) (h : ∀ b ∈ l, b ≠ 47 ∧ b ≠ 126) : encode l = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := h x (by simp)
    simp [encode, encodeByte, hx.1, hx.2, ih (fun b hb => h b (by simp [hb]))]

theorem needsNoEncoding_iff (l : List Nat) :
    needsNoEncoding l = true ↔ ∀ b ∈ l, b ≠ 47 ∧ b ≠ 126 := by
  simp [needsNoEncoding]

theorem tilde_mem_encode (x : List Nat) (h : ∃ b ∈ x, b = 47 ∨ b = 126) : 126 ∈ encode x := by
  induction x with
  | nil => simp at h
  | cons y x ih =>
    simp only [encode, List.mem_append]
    by_cases hy : y = 47 ∨ y = 126
    · left; rcases hy with rfl | rfl <;> simp [encodeByte]
    · right; apply ih
      obtain ⟨b, hb, hb'⟩ := h
      simp at hb
      rcases hb with rfl | hb
      · exact absurd hb' hy
      · exact ⟨b, hb, hb'⟩

/-- On a spelling without byte 126, the only decoding is the spelling itself. -/
theorem encode_noTilde (x l : List Nat) (he : encode x = l) (h : 126 ∉ l) : x = l := by
  have hx : ∀ b ∈ x, b ≠ 47 ∧ b ≠ 126 := by
    intro b hb
    constructor <;> intro hbad <;> exact h (he ▸ tilde_mem_encode x ⟨b, hb, by simp [hbad]⟩)
  rw [← he, encode_eq_self x hx]

/-! ### The release decoding state machine -/

/-- The byte loop of `Token::decoded` after the first tilde, as a list
function: `esc` is the release's `escaped` flag. A proof helper, not part of
the specification. -/
def decLoop : Bool → List Nat → List Nat
  | _, [] => []
  | esc, b :: r =>
    if b = 126 then decLoop true r
    else if b = 48 ∧ esc = true then 126 :: decLoop false r
    else if b = 49 ∧ esc = true then 47 :: decLoop false r
    else b :: decLoop esc r

theorem decLoop_encode (y : List Nat) : decLoop false (encode y) = y := by
  induction y with
  | nil => rfl
  | cons b y ih =>
    by_cases h47 : b = 47
    · subst h47; simp [encode, encodeByte, decLoop, ih]
    · by_cases h126 : b = 126
      · subst h126; simp [encode, encodeByte, decLoop, ih]
      · simp [encode, encodeByte, h47, h126, decLoop, ih]

theorem decode_firstTilde (x : List Nat) (i : Nat) (hi : (encode x)[i]? = some 126)
    (hpre : ∀ k x', k < i → (encode x)[k]? = some x' → x' ≠ 126) :
    (encode x).take i ++ decLoop true ((encode x).drop (i + 1)) = x := by
  induction x generalizing i with
  | nil => simp [encode] at hi
  | cons b x ih =>
    by_cases h47 : b = 47
    · subst h47
      cases i with
      | zero => simp [encode, encodeByte, decLoop, decLoop_encode]
      | succ i => exact absurd rfl (hpre 0 126 (by omega) (by simp [encode, encodeByte]))
    · by_cases h126 : b = 126
      · subst h126
        cases i with
        | zero => simp [encode, encodeByte, decLoop, decLoop_encode]
        | succ i => exact absurd rfl (hpre 0 126 (by omega) (by simp [encode, encodeByte]))
      · have he : encode (b :: x) = b :: encode x := by simp [encode, encodeByte, h47, h126]
        rw [he] at hi hpre ⊢
        cases i with
        | zero => simp at hi; exact absurd hi h126
        | succ i =>
          simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
          congr 1
          apply ih i (by simpa using hi)
          intro k x' hk hk'
          exact hpre (k + 1) x' (by omega) (by simpa using hk')

/-! ### Pointer rendering and multi-step resolution -/

theorem slash_notMem_encode (k : List Nat) : 47 ∉ encode k := by
  induction k with
  | nil => simp [encode]
  | cons b k ih =>
    simp only [encode, List.mem_append, not_or]
    refine ⟨?_, ih⟩
    unfold encodeByte
    split
    · simp
    · split <;> simp_all [eq_comm]

theorem render_head (ks : List (List Nat)) : render ks = [] ∨ (render ks).head? = some 47 := by
  cases ks with
  | nil => simp [render]
  | cons k ks => simp [render]

theorem split_unique (a b a' b' : List Nat) (ha : 47 ∉ a) (ha' : 47 ∉ a')
    (hb : b = [] ∨ b.head? = some 47) (hb' : b' = [] ∨ b'.head? = some 47)
    (h : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => simpa using h
    | cons x a' =>
      have hx : x ≠ 47 := fun hx => ha' (by simp [hx])
      simp at h
      rcases hb with rfl | hb
      · simp at h
      · rw [h] at hb; simp at hb; exact absurd hb hx
  | cons x a ih =>
    have hx : x ≠ 47 := fun hx => ha (by simp [hx])
    cases a' with
    | nil =>
      simp at h
      rcases hb' with rfl | hb'
      · simp at h
      · rw [← h] at hb'; simp at hb'; exact absurd hb' hx
    | cons y a' =>
      simp at h
      obtain ⟨rfl, h⟩ := h
      have := ih a' (fun hm => ha (by simp [hm])) (fun hm => ha' (by simp [hm])) h
      exact ⟨by rw [this.1], this.2⟩

theorem resolveFrom_cons (m p o : Nat) (t : Tree) (k : List Nat) (ks : List (List Nat)) :
    resolveFrom m p o t (k :: ks) =
      match resolveFrom m p o t [k] with
      | .ok c => resolveFrom m (p + 1) (o + 1 + (encode k).length) c ks
      | .error e => .error e := by
  cases t with
  | leaf x => simp [resolveFrom]
  | arr items =>
    simp only [resolveFrom]
    cases parseIndex m (encode k) with
    | error e => rfl
    | ok i =>
      simp only
      cases forLen i items.length with
      | error e => rfl
      | ok n =>
        simp only
        cases items[n]? with
        | none => rfl
        | some c => simp [resolveFrom]
  | obj ms =>
    simp only [resolveFrom]
    cases lookupKey k ms with
    | none => rfl
    | some c => simp [resolveFrom]

/-! ### Specification sanity facts proved here (not relied on by the contracts
unless used above) -/

/-- The specification's sanity fact `decode_encode`. -/
theorem decode_encode (x : List Nat) : decode? (encode x) = some x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    by_cases h47 : b = 47
    · subst h47; simp [encode, encodeByte, decode?, ih]
    · by_cases h126 : b = 126
      · subst h126; simp [encode, encodeByte, decode?, ih]
      · simp only [encode, encodeByte, h47, h126, if_false, List.singleton_append]
        rw [decode?.eq_def]; simp [h47, h126, ih]

/-- The specification's sanity fact `encode_injective`. -/
theorem encode_injective (x y : List Nat) (h : encode x = encode y) : x = y := by
  have hx := decode_encode x
  rw [h, decode_encode y] at hx
  exact (Option.some.inj hx).symm

/-- The specification's sanity fact `encode_length`. -/
theorem encode_length (x : List Nat) :
    x.length ≤ (encode x).length ∧ (encode x).length ≤ 2 * x.length := by
  refine ⟨?_, encode_length_le x⟩
  induction x with
  | nil => simp [encode]
  | cons b x ih =>
    have : 1 ≤ (encodeByte b).length := by
      unfold encodeByte; split
      · simp
      · split <;> simp
    simp [encode]; omega

end JsonptrAdaptedProofs.Model
