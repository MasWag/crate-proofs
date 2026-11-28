import ExtProofs.Tier2

/-!
# Support lemmas for the dropped `str` char-boundary assertions (implementation agent)

Each adapted body that replaces a checked `str` operation by a byte operation
drops `is_char_boundary(index)` (`index = 0 ∨ index = len ∨ byte at index ∉ 128..191`).
These lemmas prove that condition at each call site. `ValidUtf8` (RFC 3629
well-formedness, a real byte-level definition) is assumed only where the
release relies on the `str` invariant: the byte after a slash is the start of
the next token.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

/-- The `str::is_char_boundary` condition on a byte list. -/
def IsCharBoundary (l : List Nat) (i : Nat) : Prop :=
  i = 0 ∨ i = l.length ∨ ∃ b, l[i]? = some b ∧ ¬ (128 ≤ b ∧ b ≤ 191)

def isCont (c : Nat) : Bool := decide (128 ≤ c) && decide (c ≤ 191)

def inR (lo hi c : Nat) : Bool := decide (lo ≤ c) && decide (c ≤ hi)

/-- Length of the UTF-8 sequence a lead byte starts; 0 for an invalid lead. -/
def leadLen (b : Nat) : Nat :=
  if b ≤ 127 then 1 else if inR 194 223 b then 2 else if inR 224 239 b then 3
  else if inR 240 244 b then 4 else 0

/-- The second-byte range of Unicode Table 3-7. -/
def secondOK (b c : Nat) : Bool :=
  if b = 224 then inR 160 191 c else if b = 237 then inR 128 159 c
  else if b = 240 then inR 144 191 c else if b = 244 then inR 128 143 c else isCont c

/-- RFC 3629 / Unicode Table 3-7 well-formed UTF-8. -/
def utf8Valid : List Nat → Bool
  | [] => true
  | b :: r =>
    if leadLen b = 0 then false
    else if leadLen b = 1 then utf8Valid r
    else decide (leadLen b - 1 ≤ r.length) && (r.take (leadLen b - 1)).all isCont &&
      (match r with | c :: _ => secondOK b c | [] => false) && utf8Valid (r.drop (leadLen b - 1))
termination_by l => l.length
decreasing_by all_goals simp_wf; all_goals (simp; omega)

def ValidUtf8 (l : List Nat) : Prop := utf8Valid l = true

theorem utf8Valid_cons (b : Nat) (r : List Nat) : utf8Valid (b :: r) =
    if leadLen b = 0 then false
    else if leadLen b = 1 then utf8Valid r
    else (decide (leadLen b - 1 ≤ r.length) && (r.take (leadLen b - 1)).all isCont &&
      (match r with | c :: _ => secondOK b c | [] => false) && utf8Valid (r.drop (leadLen b - 1))) := by
  rw [utf8Valid.eq_def]

theorem leadLen_cont (c : Nat) (h1 : 128 ≤ c) (h2 : c ≤ 191) : leadLen c = 0 := by
  unfold leadLen inR; split_ifs <;> (try simp_all) <;> omega

theorem leadLen_ge2 (b : Nat) (hb : ¬ b ≤ 127) (h0 : leadLen b ≠ 0) : 2 ≤ leadLen b := by
  unfold leadLen at h0 ⊢; simp only [hb, ↓reduceIte] at h0 ⊢
  split_ifs at h0 ⊢ <;> omega

theorem utf8_head_not_cont (c : Nat) (r : List Nat) (h : utf8Valid (c :: r) = true) : isCont c = false := by
  by_contra hc
  simp only [isCont, Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [utf8Valid_cons, leadLen_cont c hc.1 hc.2] at h; simp at h

/-- In valid UTF-8, the byte after an ASCII byte is not a continuation byte. -/
theorem utf8_after_ascii : ∀ (n : Nat) (l : List Nat), l.length ≤ n → utf8Valid l = true →
    ∀ i b, l[i]? = some b → b ≤ 127 → ∀ c, l[i + 1]? = some c → isCont c = false := by
  intro n
  induction n with
  | zero => intro l hl _ i b hi; simp [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hi
  | succ n ih =>
    intro l hl hv i b hi hb c hc
    cases l with
    | nil => simp at hi
    | cons a r =>
      by_cases ha : a ≤ 127
      · have h1 : leadLen a = 1 := by simp [leadLen, ha]
        rw [utf8Valid_cons, h1] at hv; simp at hv
        cases i with
        | zero =>
          cases r with
          | nil => simp at hc
          | cons c' r' => simp at hc; subst hc; exact utf8_head_not_cont _ _ hv
        | succ i => exact ih r (by simp at hl; omega) hv i b (by simpa using hi) hb c (by simpa using hc)
      · have h0 : leadLen a ≠ 0 := by intro h; rw [utf8Valid_cons, h] at hv; simp at hv
        have h2 := leadLen_ge2 a ha h0
        rw [utf8Valid_cons] at hv
        simp only [h0, ↓reduceIte, show leadLen a ≠ 1 by omega, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] at hv
        obtain ⟨⟨⟨hlen, hconts⟩, _⟩, hrest⟩ := hv
        set k := leadLen a - 1 with hk
        cases i with
        | zero => simp at hi; omega
        | succ i =>
          simp at hi hc
          by_cases hik : i < k
          · have hm : b ∈ r.take k := by
              rw [List.mem_iff_getElem?]; exact ⟨i, by rw [List.getElem?_take]; simp [hik, hi]⟩
            have := hconts b hm
            simp [isCont] at this; omega
          · have hi' : (r.drop k)[i - k]? = some b := by rw [List.getElem?_drop]; rwa [show k + (i - k) = i by omega]
            have hc' : (r.drop k)[i - k + 1]? = some c := by
              rw [List.getElem?_drop]; rwa [show k + (i - k + 1) = i + 1 by omega]
            exact ih (r.drop k) (by simp at hl ⊢; omega) hrest (i - k) b hi' hb c hc'

theorem boundary_after_ascii (l : List Nat) (hv : ValidUtf8 l) (i b : Nat) (hi : l[i]? = some b)
    (hb : b ≤ 127) : IsCharBoundary l (i + 1) := by
  rcases h : l[i + 1]? with _ | c
  · right; left
    have h1 := (List.getElem?_eq_some_iff.mp hi).1
    have h2 := List.getElem?_eq_none_iff.mp h
    omega
  · right; right
    refine ⟨c, h, ?_⟩
    have := utf8_after_ascii l.length l (le_refl _) hv i b hi hb c h
    simp [isCont] at this; omega

theorem boundary_at_slash (l : List Nat) (i : Nat) (h : l[i]? = some 47) : IsCharBoundary l i :=
  Or.inr (Or.inr ⟨47, h, by omega⟩)

/-! ## The call sites -/

/-- `split_at_offset_adapted`: the dropped boundary check of `str::split_at(offset)`
holds whenever the split is taken. No premise. -/
theorem splitAtOffset_charBoundary (xs : Slice U8) (off : Usize) (h t : Slice U8)
    (hr : jsonptr.adapted_api.split_at_offset_adapted xs off = .ok (some (h, t))) :
    IsCharBoundary (bytes xs) off.val := by
  obtain ⟨r, hr', hm⟩ := ok_of_spec (splitAtOffset_spec xs off)
  rw [hr] at hr'; simp only [Result.ok.injEq] at hr'; subst hr'
  simp only [opbytes, Option.map_some, splitAtOffset] at hm
  split at hm
  · next h47 => exact boundary_at_slash _ _ h47
  · simp at hm

/-- `pop_front_adapted`: `split_off(idx + 1)` where `idx` is the first slash of
`&buf[1..]` (the `find_slash_adapted` postcondition): the split is at a slash. -/
theorem popFront_splitOff_charBoundary (l : List Nat) (j : Nat) (hj : (l.drop 1)[j]? = some 47) :
    IsCharBoundary l (j + 1) := by
  apply boundary_at_slash
  rw [List.getElem?_drop] at hj; rwa [Nat.add_comm]

/-- `split_front_adapted` (target 6), `front_adapted` and `pop_front_adapted`:
the slice `&s[1..]` of a nonempty valid pointer is at a char boundary, given the
`str` invariant. -/
theorem slice_one_charBoundary (l : List Nat) (hp : ValidPointer l) (hu : ValidUtf8 l) (hne : l ≠ []) :
    IsCharBoundary l 1 := by
  have h0 : l[0]? = some 47 := by
    rcases slashLed_of_valid l hp with h | h
    · exact absurd h hne
    · cases l with
      | nil => exact absurd rfl hne
      | cons a r => simpa using h
  exact boundary_after_ascii l hu 0 47 h0 (by omega)

/-- `push_front_adapted`: `insert(0, '/')` is at 0, and `insert_str(1, t)` on
`"/" ++ old` is at a boundary because `old` is empty or starts with `/`. -/
theorem pushFront_charBoundary (old : List Nat) (hp : ValidPointer old) :
    IsCharBoundary old 0 ∧ IsCharBoundary (47 :: old) 1 := by
  refine ⟨Or.inl rfl, ?_⟩
  rcases slashLed_of_valid old hp with h | h
  · subst h; right; left; rfl
  · cases old with
    | nil => right; left; rfl
    | cons a r => simp at h; subst h; exact boundary_at_slash _ _ rfl

/-- `pop_back_adapted`: `split_off(idx + 1)` where `idx` is the last slash; the
next byte starts the last token, given the `str` invariant. -/
theorem popBack_splitOff_charBoundary (l : List Nat) (hu : ValidUtf8 l) (i : Nat) (h : l[i]? = some 47) :
    IsCharBoundary l (i + 1) :=
  boundary_after_ascii l hu i 47 h (by omega)

/-! ## Call-site forms over the generated functions -/

/-- `pop_back_adapted`: the generated body computes `i ← rfind_slash_ext (deref buf)`
and splits at `i + 1`; that index is a char boundary of the buffer. -/
theorem popBack_generated_charBoundary (buf : alloc.vec.Vec U8) (hu : ValidUtf8 (vbytes buf)) (i : Usize)
    (h : jsonptr.adapted_api.rfind_slash_ext (alloc.vec.Vec.deref buf) = .ok (some i)) :
    IsCharBoundary (vbytes buf) (i.val + 1) := by
  obtain ⟨o, ho, hp⟩ := ok_of_spec (rfindSlash_spec (alloc.vec.Vec.deref buf))
  rw [h] at ho; simp only [Result.ok.injEq] at ho; subst ho
  obtain ⟨_, h47, _⟩ := hp
  have : bytes (alloc.vec.Vec.deref buf) = vbytes buf := by simp [bytes, vbytes, alloc.vec.Vec.deref]
  rw [this] at h47
  exact popBack_splitOff_charBoundary _ hu _ h47

/-- `pop_front_adapted`: the generated body computes `j ← find_slash_adapted s`
for `s = buf[1..]` and splits at `j + 1`; that index is a char boundary. -/
theorem popFront_generated_charBoundary (buf : alloc.vec.Vec U8) (s : Slice U8)
    (hs : s.val = buf.val.drop 1) (j : Usize)
    (h : jsonptr.pointer.find_slash_adapted s = .ok (some j)) :
    IsCharBoundary (vbytes buf) (j.val + 1) := by
  obtain ⟨o, ho, hp⟩ := ok_of_spec (findSlash_spec s)
  rw [h] at ho; simp only [Result.ok.injEq] at ho; subst ho
  obtain ⟨_, h47, _⟩ := hp
  apply popFront_splitOff_charBoundary
  have : bytes s = (vbytes buf).drop 1 := by simp [bytes, vbytes, hs, List.map_drop]
  rwa [this] at h47

/-- `split_front_adapted`, `front_adapted`, `pop_front_adapted`: each slices its
nonempty input at the constant index 1. -/
theorem sliceOne_generated_charBoundary (xs : Slice U8) (hp : ValidPtr xs) (hu : ValidUtf8 (bytes xs))
    (hne : xs.length ≠ 0) : IsCharBoundary (bytes xs) 1 :=
  slice_one_charBoundary _ hp hu (by intro h; apply hne; simpa using congrArg List.length h)

end JsonptrExtProofs
