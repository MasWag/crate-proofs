import Statements.Common
import ExtProofs.Model

/-!
# The adapted `Tokens` iterator (implementation agent)

`piecesOf it` is the list of pieces the split state still yields. One call of
`tokens_next_adapted` yields its head and leaves its tail.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = .ok x ∧ P x := by
  cases hm : m with
  | ret out => exact ⟨out, rfl, (spec_ok out).mp (hm ▸ h)⟩
  | div => exact False.elim (spec_div.mp (hm ▸ h))
  | vis e k => exact False.elim ((spec_vis e k).mp (hm ▸ h))

@[simp] theorem bytes_length (s : Slice U8) : (bytes s).length = s.length := by
  simp [bytes]

theorem bytes_val (s : Slice U8) : bytes s = s.val.map (fun b => b.val) := rfl

theorem bytes_eq_of_val {s t : Slice U8} (h : s.val = t.val) : bytes s = bytes t := by
  simp [bytes, h]

/-- The pieces a split state still yields. -/
def piecesOf (it : jsonptr.adapted_api.TokensAdapted) : List (List Nat) :=
  if it.finished then [] else splitSlash ((bytes it.haystack).drop it.start.val)

/-- The split state's own invariant. -/
def TokInv (it : jsonptr.adapted_api.TokensAdapted) : Prop :=
  it.start.val ≤ it.haystack.length

theorem bytes_slice (h : Slice U8) (a b : Nat) :
    (h.val.slice a b).map (fun x => x.val) = ((bytes h).drop a).take (b - a) := by
  simp [List.slice, bytes, List.map_take, List.map_drop]

/-- The search loop of `tokens_next_adapted`. -/
theorem tokensNextLoop_spec (h : Slice U8) (st : Usize) (fin : Bool) (j : Usize)
    (hst : st.val ≤ j.val) (hj : j.val ≤ h.length)
    (hno : ∀ k, st.val ≤ k → k < j.val → (bytes h)[k]? ≠ some 47) :
    jsonptr.adapted_api.tokens_next_adapted_loop h st fin j ⦃ (s1 : Slice U8) (i : Usize) (b : Bool) =>
      (∃ e, st.val ≤ e ∧ e < h.length ∧ (bytes h)[e]? = some 47 ∧
        (∀ k, st.val ≤ k → k < e → (bytes h)[k]? ≠ some 47) ∧
        bytes s1 = ((bytes h).drop st.val).take (e - st.val) ∧ i.val = e + 1 ∧ b = fin) ∨
      ((∀ k, st.val ≤ k → k < h.length → (bytes h)[k]? ≠ some 47) ∧
        bytes s1 = (bytes h).drop st.val ∧ i = st ∧ b = true) ⦄ := by
  unfold jsonptr.adapted_api.tokens_next_adapted_loop
  apply loop.spec_decr_nat (fun j : Usize => h.length - j.val)
    (fun j : Usize => st.val ≤ j.val ∧ j.val ≤ h.length ∧
      ∀ k, st.val ≤ k → k < j.val → (bytes h)[k]? ≠ some 47)
  · rintro j ⟨h1, h2, h3⟩
    simp only [jsonptr.adapted_api.tokens_next_adapted_loop.body]
    split
    next hlt =>
      have hjl : j.val < h.length := by scalar_tac
      step as ⟨x, hx⟩
      have hxj : (bytes h)[j.val]? = some x.val := by
        simp [bytes, List.getElem?_map, List.getElem?_eq_getElem hjl, hx]
      split
      next heq =>
        step as ⟨s1, hs1, _⟩
        step as ⟨i4, hi4⟩
        left
        refine ⟨j.val, h1, hjl, by rw [hxj, heq]; rfl, h3, ?_, by simp [hi4]⟩
        simp only [bytes_val, hs1, bytes_slice]
      next hne =>
        step as ⟨i4, hi4⟩
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro k hk1 hk2
        by_cases hkj : k < j.val
        · exact h3 k hk1 hkj
        · have : k = j.val := by scalar_tac
          subst this; rw [hxj]; intro e
          apply hne; simp at e; exact UScalar.eq_of_val_eq (by simpa using e)
    next hge =>
      step as ⟨s1, hs1, _⟩
      right
      refine ⟨fun k hk1 hk2 => h3 k hk1 (by scalar_tac), ?_⟩
      simp [bytes, hs1, List.map_drop]
  · exact ⟨hst, hj, hno⟩

theorem noSlash_drop_take (l : List Nat) (a e : Nat)
    (hno : ∀ k, a ≤ k → k < e → l[k]? ≠ some 47) : 47 ∉ (l.drop a).take (e - a) := by
  intro hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
  have hk' := hk
  rw [List.getElem?_take] at hk'
  split at hk'
  · next hlt =>
    rw [List.getElem?_drop] at hk'
    exact hno (a + k) (by omega) (by omega) hk'
  · simp at hk'

theorem noSlash_drop (l : List Nat) (a : Nat)
    (hno : ∀ k, a ≤ k → k < l.length → l[k]? ≠ some 47) : 47 ∉ l.drop a := by
  intro hm
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
  rw [List.getElem?_drop] at hk
  exact hno (a + k) (by omega) (List.getElem?_eq_some_iff.mp hk).1 hk

/-- One step of the iterator: it yields the head of the remaining pieces. -/
theorem tokensNext_spec (it : jsonptr.adapted_api.TokensAdapted) (hinv : TokInv it) :
    jsonptr.adapted_api.tokens_next_adapted it ⦃ (o : Option (Slice U8)) it' =>
      o.map bytes = (piecesOf it).head? ∧ piecesOf it' = (piecesOf it).tail ∧ TokInv it' ∧
      it'.haystack = it.haystack ⦄ := by
  unfold jsonptr.adapted_api.tokens_next_adapted
  split
  next hf =>
    apply (spec_ok _).mpr
    simp [piecesOf, hf, hinv]
  next hf =>
    have hfin : it.finished = false := by simpa using hf
    apply spec_bind (tokensNextLoop_spec it.haystack it.start it.finished it.start
      (le_refl _) hinv (fun k h1 h2 => by omega))
    rintro ⟨s1, i, b⟩ hpost
    apply (spec_ok _).mpr
    rcases hpost with ⟨e, he1, he2, he3, he4, hs1, hi, hb⟩ | ⟨hno, hs1, hi, hb⟩
    · -- a slash at `e`: the piece before it, and the rest after it
      have hsplit : (bytes it.haystack).drop it.start.val =
          ((bytes it.haystack).drop it.start.val).take (e - it.start.val) ++
            47 :: (bytes it.haystack).drop (e + 1) := by
        have hlen : e < (bytes it.haystack).length := by simpa using he2
        conv_lhs => rw [← List.take_append_drop (e - it.start.val) ((bytes it.haystack).drop it.start.val)]
        congr 1
        rw [List.drop_drop, show it.start.val + (e - it.start.val) = e by omega]
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        rw [List.getElem?_eq_getElem hlen] at he3; simpa using he3
      have hns := noSlash_drop_take (bytes it.haystack) it.start.val e he4
      have hpieces : piecesOf it = (((bytes it.haystack).drop it.start.val).take (e - it.start.val)) ::
          splitSlash ((bytes it.haystack).drop (e + 1)) := by
        simp only [piecesOf, hfin, Bool.false_eq_true, ↓reduceIte]
        conv_lhs => rw [hsplit]
        rw [splitSlash_append_slash, splitSlash_noSlash _ hns]
        rfl
      refine ⟨by simp [hpieces, hs1], ?_, ?_, rfl⟩
      · rw [hpieces]
        simp only [piecesOf, hb, hfin, Bool.false_eq_true, ↓reduceIte, List.tail_cons]
        congr 2
      · show i.val ≤ it.haystack.length
        rw [hi]; omega
    · have hns := noSlash_drop (bytes it.haystack) it.start.val (fun k h1 h2 => hno k h1 (by simpa using h2))
      have hpieces : piecesOf it = [(bytes it.haystack).drop it.start.val] := by
        simp [piecesOf, hfin, splitSlash_noSlash _ hns]
      refine ⟨by simp [hpieces, hs1], ?_, ?_, rfl⟩
      · rw [hpieces]; simp [piecesOf, hb]
      · show i.val ≤ it.haystack.length
        rw [hi]; exact hinv

/-- After `Pointer::tokens`, the remaining pieces are the encoded tokens. -/
theorem tokens_spec (xs : Slice U8) :
    jsonptr.adapted_api.tokens_adapted xs ⦃ it =>
      piecesOf it = encodedTokens (bytes xs) ∧ TokInv it ∧ it.haystack = xs ⦄ := by
  unfold jsonptr.adapted_api.tokens_adapted
  apply spec_bind (tokensNext_spec { haystack := xs, start := 0#usize, finished := false }
    (by simp [TokInv]))
  rintro ⟨o, it'⟩ ⟨_, hp, hinv, hh⟩
  apply (spec_ok _).mpr
  refine ⟨?_, hinv, hh⟩
  rw [hp]
  simp [piecesOf, encodedTokens, List.drop_one]

end JsonptrExtProofs
