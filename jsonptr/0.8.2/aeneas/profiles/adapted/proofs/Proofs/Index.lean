import Proofs.Token

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

/-! ## Target 5: `Index::from_str` / `Token::to_index` -/

theorem isAsciiDigit_eq (x : U8) :
    jsonptr.core.num.U8.is_ascii_digit x = .ok (isDigit x.val) := by
  unfold jsonptr.core.num.U8.is_ascii_digit isDigit
  split <;> rename_i h
  · have h1 : 48 ≤ x.val := by scalar_tac
    by_cases h2 : x.val ≤ 57
    · have : x ≤ 57#u8 := by scalar_tac
      simp [h1, h2, this]
    · have : ¬ x ≤ 57#u8 := by scalar_tac
      simp [h1, h2, this]
  · have h1 : ¬ 48 ≤ x.val := by scalar_tac
    simp [h1]

theorem nonDigit_spec (s : Slice U8) :
    jsonptr.index.position_non_digit_adapted s ⦃ FirstIdx (fun b => isDigit b.val = false) s.val ⦄ := by
  unfold jsonptr.index.position_non_digit_adapted jsonptr.index.position_non_digit_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ (k : Nat) x, k < i.val → s.val[k]? = some x → isDigit x.val ≠ false)
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.index.position_non_digit_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi)
      intro x hx
      have hx' : s.val[i.val]? = some x := by rw [List.getElem?_eq_getElem hi, hx]
      rw [isAsciiDigit_eq]
      simp only [bind_ok, bind_tc_ok]
      split
      next hd =>
        step as ⟨i', hi'⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k y hk hy
        by_cases hki : k < i.val
        · exact hall k y hki hy
        · have : k = i.val := by scalar_tac
          subst this
          rw [hx'] at hy; cases hy; simp [hd]
      next hd =>
        apply (spec_ok _).mpr
        exact ⟨⟨x, hx', by simpa using hd⟩, fun k y hk hy => by simpa using hall k y hk hy⟩
    next hge =>
      apply (spec_ok _).mpr
      intro k y hy
      have : k < s.val.length := (List.getElem?_eq_some_iff.mp hy).1
      simpa using hall k y (by scalar_tac) hy
  · exact ⟨by scalar_tac, fun k x hk => by scalar_tac⟩

theorem firstNonDigit_of_firstIdx (s : Slice U8) (o : Option Usize)
    (h : FirstIdx (fun b => isDigit b.val = false) s.val o) :
    firstNonDigit (bytes s) = o.map (fun j => j.val) := by
  unfold firstNonDigit
  cases o with
  | none =>
    simp only [Option.map_none]
    apply Model.firstNonDigitFrom_none
    intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
    have := h k x hk
    simpa using this
  | some j =>
    obtain ⟨⟨x, hx, hbad⟩, hpre⟩ := h
    have hj : j.val < s.val.length := (List.getElem?_eq_some_iff.mp hx).1
    simp only [Option.map_some]
    rw [Model.firstNonDigitFrom_some (bytes s) 0 j.val (by simpa using hj)]
    · simp
    · rw [bytes_getElem]; have := (List.getElem?_eq_some_iff.mp hx).2; rw [this]; exact hbad
    · intro k hk
      rw [bytes_getElem]
      have hk' : k < s.val.length := by omega
      have := hpre k (s.val[k]) hk (List.getElem?_eq_getElem hk')
      simpa using this

def DigitsPost (L : List Nat) : core.result.Result Usize jsonptr.index.IntErrorKindAdapted → Prop
  | .Ok n => n.val = decimalValue L ∧ decimalValue L ≤ Usize.max
  | .Err k => k = .PosOverflow ∧ Usize.max < decimalValue L

theorem digitsLoop_spec (s : Slice U8) (hdig : ∀ (k : Nat) x, s.val[k]? = some x → isDigit x.val = true) :
    jsonptr.index.parse_usize_digits_adapted_loop s 0#usize 0#usize ⦃ DigitsPost (bytes s) ⦄ := by
  have hlen : (bytes s).length = s.length := bytes_length s
  unfold jsonptr.index.parse_usize_digits_adapted_loop
  apply loop.spec_decr_nat (fun st : Usize × Usize => s.length - st.2.val)
    (fun st => st.2.val ≤ s.length ∧ st.1.val = decimalValue ((bytes s).take st.2.val))
  · rintro ⟨acc, i⟩ ⟨hle, hacc⟩
    simp only [jsonptr.index.parse_usize_digits_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi)
      intro x hx
      have hx' : s.val[i.val]? = some x := by rw [List.getElem?_eq_getElem hi, hx]
      have hd := hdig i.val x hx'
      have h48 : 48 ≤ x.val := by simp [isDigit] at hd; omega
      have htake : decimalValue ((bytes s).take (i.val + 1)) = 10 * acc.val + (x.val - 48) := by
        rw [Model.decimalValue_take_succ _ _ (by rw [hlen]; exact hi), ← hacc,
          bytes_getElem s i.val (by rw [hlen]; exact hi), ← hx]
      have hmono : decimalValue ((bytes s).take (i.val + 1)) ≤ decimalValue (bytes s) := by
        have := Model.decimalValue_take_mono (bytes s) (i.val + 1) (bytes s).length (by rw [hlen]; omega)
        rwa [List.take_length] at this
      step as ⟨d, hd'⟩
      simp only [lift, bind_ok, bind_tc_ok]
      have hcast : (UScalar.cast UScalarTy.Usize d).val = x.val - 48 := by
        rw [U8.cast_Usize_val_eq]; omega
      have hmul := Usize.checked_mul_bv_spec acc 10#usize
      split
      next hnone =>
        rw [hnone] at hmul
        apply (spec_ok _).mpr
        simp only [DigitsPost]
        refine ⟨trivial, ?_⟩
        simp at hmul; omega
      next m hsome =>
        rw [hsome] at hmul
        obtain ⟨_, hm, _⟩ := hmul
        have hadd := Usize.checked_add_bv_spec m (UScalar.cast UScalarTy.Usize d)
        split
        next hnone =>
          rw [hnone] at hadd
          apply (spec_ok _).mpr
          simp only [DigitsPost]
          refine ⟨trivial, ?_⟩
          simp at hm; omega
        next a hsome2 =>
          rw [hsome2] at hadd
          obtain ⟨_, ha, _⟩ := hadd
          step as ⟨i', hi'⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi', htake, ha, hm, hcast]; simp; ring
    next hge =>
      apply (spec_ok _).mpr
      have hi : i.val = (bytes s).length := by scalar_tac
      simp only [DigitsPost]
      rw [hi, List.take_length] at hacc
      exact ⟨hacc, by rw [← hacc]; scalar_tac⟩
  · exact ⟨by scalar_tac, by simp [decimalValue]⟩

/-- The checked accumulation on all-digit input, with its outcome as the
model's last three cases of `parseIndex`. -/
theorem parseDigits_eq (s : Slice U8) (hdig : ∀ (k : Nat) x, s.val[k]? = some x → isDigit x.val = true) :
    ∃ r, jsonptr.index.parse_usize_digits_adapted s = .ok r ∧
      indexOutcome (match r with
        | .Ok n => .Ok (jsonptr.index.Index.Num n)
        | .Err k => .Err (jsonptr.index.ParseIndexErrorAdapted.InvalidInteger k)) =
      (if bytes s = [] then .error (.invalidInteger .empty)
       else if decimalValue (bytes s) ≤ Usize.max then .ok (.num (decimalValue (bytes s)))
       else .error (.invalidInteger .posOverflow)) := by
  by_cases hlen : s.length = 0
  · have hnil : bytes s = [] := by simp [bytes, List.length_eq_zero_iff.mp hlen]
    refine ⟨.Err .Empty, ?_, ?_⟩
    · simp [jsonptr.index.parse_usize_digits_adapted, core.slice.Slice.is_empty, hlen]
    · simp [hnil, indexOutcome, indexError, intKind]
  · have hne : bytes s ≠ [] := by
      intro h; apply hlen; rw [← bytes_length, h]; rfl
    obtain ⟨r, hr, hpost⟩ := ok_of_spec (digitsLoop_spec s hdig)
    refine ⟨r, ?_, ?_⟩
    · simp [jsonptr.index.parse_usize_digits_adapted, core.slice.Slice.is_empty, hlen, hr]
    · cases r with
      | Ok n =>
        obtain ⟨hn, hle⟩ := hpost
        simp [hne, hle, indexOutcome, index, hn]
      | Err k =>
        obtain ⟨rfl, hgt⟩ := hpost
        have : ¬ decimalValue (bytes s) ≤ Usize.max := by omega
        simp [hne, this, indexOutcome, indexError, intKind]

theorem len_eq_one_iff (s : Slice U8) : (s.len = 1#usize) ↔ s.val.length = 1 := by
  constructor
  · intro h; have := congrArg UScalar.val h; simpa using this
  · intro h; apply UScalar.eq_of_val_eq; simpa using h

theorem u8_eq_lit_iff {x y : U8} : x = y ↔ x.val = y.val :=
  ⟨fun h => h ▸ rfl, fun h => UScalar.eq_of_val_eq h⟩

/-- The model's first-error precedence, unfolded on the first byte. -/
theorem parseIndex_cons (c : Nat) (rest : List Nat) :
    parseIndex Usize.max (c :: rest) =
      if rest = [] ∧ c = 45 then .ok .next
      else if c = 48 ∧ rest ≠ [] then .error .leadingZeros
      else match firstNonDigit (c :: rest) with
        | some off => .error (.invalidCharacter off)
        | none =>
          if decimalValue (c :: rest) ≤ Usize.max then .ok (.num (decimalValue (c :: rest)))
          else .error (.invalidInteger .posOverflow) := by
  unfold parseIndex
  by_cases h1 : rest = [] ∧ c = 45
  · obtain ⟨rfl, rfl⟩ := h1; simp
  · have h1' : ¬ (c :: rest = [45]) := by
      intro h; apply h1; simp at h; exact ⟨h.2, h.1⟩
    rw [if_neg h1', if_neg h1]
    by_cases h2 : c = 48 ∧ rest ≠ []
    · rw [if_pos h2, if_pos]; simp [h2.1]; exact h2.2
    · rw [if_neg h2, if_neg]
      · cases firstNonDigit (c :: rest) <;> simp
      · intro h; apply h2; simp at h; exact ⟨h.1, h.2 h.1⟩

/-- Target 5, `Index::from_str` / `Token::to_index`. -/
theorem fromStrAdapted : IndexContract := by
  intro s
  obtain ⟨o, ho, hfi⟩ := ok_of_spec (nonDigit_spec s)
  have hfnd := firstNonDigit_of_firstIdx s o hfi
  by_cases hemp : s.val.length = 0
  · -- empty input: no non-digit, `Empty`
    have hnil : s.val = [] := List.length_eq_zero_iff.mp hemp
    have hb : bytes s = [] := by simp [bytes, hnil]
    have hdig : ∀ (k : Nat) x, s.val[k]? = some x → isDigit x.val = true := by
      intro k x hk; simp [hnil] at hk
    obtain ⟨r, hr, hpost⟩ := parseDigits_eq s hdig
    have ho' : o = none := by
      cases o with
      | none => rfl
      | some j => obtain ⟨⟨x, hx, _⟩, _⟩ := hfi; simp [hnil] at hx
    subst ho'
    have h1 : ¬ s.val.length = 1 := by omega
    rw [hb] at hpost
    cases r <;>
    · refine ⟨_, ?_, hpost.trans (by simp [parseIndex, hb, firstNonDigit, firstNonDigitFrom])⟩
      simp [jsonptr.index.from_str_adapted, ho, hr, core.slice.Slice.is_empty, (len_eq_one_iff s), h1,
        Slice.length, hemp]
  · obtain ⟨c, rest, hs⟩ : ∃ c rest, s.val = c :: rest := by
      cases h : s.val with
      | nil => simp [h] at hemp
      | cons c rest => exact ⟨c, rest, rfl⟩
    have hb : bytes s = c.val :: rest.map (fun b => b.val) := by simp [bytes, hs]
    obtain ⟨c', hidx, hc'⟩ := ok_of_spec (Slice.index_usize_spec s 0#usize (by scalar_tac))
    have hcc : c' = c := by simp [hc', hs]
    subst hcc
    have hne : ¬ s.length = 0 := hemp
    have hlen1 : (s.len = 1#usize) ↔ rest = [] := by rw [len_eq_one_iff, hs]; simp
    have h45 : (c' = 45#u8) ↔ c'.val = 45 := by rw [u8_eq_lit_iff]; simp
    have h48 : (c' = 48#u8) ↔ c'.val = 48 := by rw [u8_eq_lit_iff]; simp
    rw [hb, parseIndex_cons]
    rw [hb] at hfnd
    have hs0 : decide (s.length = 0) = false := by simp [hne]
    cases o with
    | some j =>
      simp only [Option.map_some] at hfnd
      simp only [jsonptr.index.from_str_adapted, ho, hidx, core.slice.Slice.is_empty, bind_ok, hs0,
        Bool.false_eq_true, if_false, hlen1, h45, h48]
      clear h45 h48 hlen1 hidx ho hc' hfi hs0 hne hemp hb hs
      split_ifs <;> refine ⟨_, rfl, ?_⟩ <;> simp_all [indexOutcome, index, indexError]
    | none =>
      simp only [Option.map_none] at hfnd
      have hdig : ∀ (k : Nat) x, s.val[k]? = some x → isDigit x.val = true := by
        intro k x hk; simpa using hfi k x hk
      obtain ⟨r, hr, hpost⟩ := parseDigits_eq s hdig
      rw [hb] at hpost
      simp only [List.cons_ne_nil, if_false] at hpost
      cases r <;>
      · simp only [jsonptr.index.from_str_adapted, ho, hr, hidx, core.slice.Slice.is_empty, bind_ok, hs0,
          Bool.false_eq_true, if_false, hlen1, h45, h48]
        clear h45 h48 hlen1 hidx ho hc' hfi hs0 hne hemp hb hs hr hdig
        split_ifs <;> refine ⟨_, rfl, ?_⟩ <;> simp_all [indexOutcome, index, indexError]

end JsonptrAdaptedProofs
