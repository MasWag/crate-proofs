import Proofs.Token

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

/-! ## Targets 2 and 3: `Token::new` and `Token::decoded` -/

theorem usize_max_of_isize : (2 * Isize.max + 1 : Int) = Usize.max := by
  rw [Isize.max_def, Usize.max_def, Isize.numBits_def, Usize.numBits_def]
  simp only [IScalarTy.Isize_numBits_eq, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem sliceBound_le {s : Slice U8} (h : SliceBound s) : 2 * s.length + 1 ≤ Usize.max := by
  have := usize_max_of_isize
  unfold SliceBound at h
  omega

theorem extend_ok (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    ∃ w, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = .ok w ∧ w.val = v.val ++ s.val := by
  obtain ⟨l, hl, hlv⟩ := ok_of_spec (List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val)
    (fun x _ => rfl))
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos h]
  simp only [hl, bind_tc_ok, bind_ok]
  exact ⟨_, rfl, by rw [alloc.vec.Vec.from_val, hlv.1]⟩

theorem prefix_ok (s : Slice U8) (i : Usize) (hi : i.val ≤ s.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) s { «end» := i } =
      .ok (Slice.from (s.val.take i.val) (by have := s.property; simp only [List.length_take]; omega)) := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index]
  split
  · simp [Slice.from]; rfl
  · omega

theorem slashTilde_spec (s : Slice U8) :
    jsonptr.token.position_slash_or_tilde_adapted s
      ⦃ FirstIdx (fun b => b = 47#u8 ∨ b = 126#u8) s.val ⦄ := by
  unfold jsonptr.token.position_slash_or_tilde_adapted jsonptr.token.position_slash_or_tilde_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ (k : Nat) x, k < i.val → s.val[k]? = some x → ¬ (x = 47#u8 ∨ x = 126#u8))
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.token.position_slash_or_tilde_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi)
      intro x hx
      have hx' : s.val[i.val]? = some x := by rw [List.getElem?_eq_getElem hi, hx]
      split
      next heq => exact (spec_ok _).mpr ⟨⟨x, hx', Or.inl heq⟩, hall⟩
      next hne =>
        split
        next heq => exact (spec_ok _).mpr ⟨⟨x, hx', Or.inr heq⟩, hall⟩
        next hne2 =>
          step as ⟨i', hi'⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro k y hk hy
          by_cases hki : k < i.val
          · exact hall k y hki hy
          · have : k = i.val := by scalar_tac
            subst this
            rw [hx'] at hy; cases hy; rintro (h | h) <;> contradiction
    next hge =>
      apply (spec_ok _).mpr
      intro k y hy
      have : k < s.val.length := (List.getElem?_eq_some_iff.mp hy).1
      exact hall k y (by scalar_tac) hy
  · exact ⟨by scalar_tac, fun k x hk => by scalar_tac⟩

theorem tilde_spec (s : Slice U8) :
    jsonptr.token.position_tilde_adapted s ⦃ FirstIdx (fun b => b = 126#u8) s.val ⦄ := by
  unfold jsonptr.token.position_tilde_adapted jsonptr.token.position_tilde_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => s.length - i.val)
    (fun i => i.val ≤ s.length ∧ ∀ (k : Nat) x, k < i.val → s.val[k]? = some x → ¬ x = 126#u8)
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.token.position_tilde_adapted_loop.body, jsonptr.token.ENC_PREFIX]
    split
    next hlt =>
      have hi : i.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s i hi)
      intro x hx
      have hx' : s.val[i.val]? = some x := by rw [List.getElem?_eq_getElem hi, hx]
      split
      next heq => exact (spec_ok _).mpr ⟨⟨x, hx', heq⟩, hall⟩
      next hne =>
        step as ⟨i', hi'⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro k y hk hy
        by_cases hki : k < i.val
        · exact hall k y hki hy
        · have : k = i.val := by scalar_tac
          subst this
          rw [hx'] at hy; cases hy; exact hne
    next hge =>
      apply (spec_ok _).mpr
      intro k y hy
      have : k < s.val.length := (List.getElem?_eq_some_iff.mp hy).1
      exact hall k y (by scalar_tac) hy
  · exact ⟨by scalar_tac, fun k x hk => by scalar_tac⟩

theorem vbytes_push (v : alloc.vec.Vec U8) (x : U8) (w : alloc.vec.Vec U8) (h : w.val = v.val ++ [x]) :
    vbytes w = vbytes v ++ [x.val] := by
  simp [vbytes, h]

theorem vbytes_length (v : alloc.vec.Vec U8) : (vbytes v).length = v.length := by
  simp [vbytes]

theorem push_spec' (v : alloc.vec.Vec U8) (x : U8) (h : v.length < Usize.max) :
    alloc.vec.Vec.push v x ⦃ w => vbytes w = vbytes v ++ [x.val] ∧ w.length = v.length + 1 ⦄ := by
  apply spec_mono (alloc.vec.Vec.push_spec v x h)
  intro w hw
  exact ⟨vbytes_push v x w hw, by simp [alloc.vec.Vec.length, hw]⟩

theorem encodeLoop_spec (s : Slice U8) (hb : 2 * s.length + 1 ≤ Usize.max) (v : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ s.length) (hv : vbytes v = encode ((bytes s).take i.val)) :
    jsonptr.token.new_adapted_loop s v i ⦃ w => vbytes w = encode (bytes s) ⦄ := by
  have hlen : (bytes s).length = s.length := bytes_length s
  unfold jsonptr.token.new_adapted_loop
  apply loop.spec_decr_nat (fun st : alloc.vec.Vec U8 × Usize => s.length - st.2.val)
    (fun st => st.2.val ≤ s.length ∧ vbytes st.1 = encode ((bytes s).take st.2.val))
  · rintro ⟨v, k⟩ ⟨hk, hv⟩
    simp only at hk hv
    have hvl : v.length ≤ 2 * k.val := by
      rw [← vbytes_length, hv]
      have := Model.encode_length_le ((bytes s).take k.val); simp at this; omega
    simp only [jsonptr.token.new_adapted_loop.body]
    split
    next hlt =>
      have hk' : k.val < s.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec s k hk')
      intro x hx
      have hL := bytes_getElem? s hk' hx
      have hstep := Model.encode_take_succ (bytes s) k.val (by rw [hlen]; exact hk')
      rw [(List.getElem?_eq_some_iff.mp hL).2] at hstep
      apply spec_bind (Pₘ := fun w => vbytes w = vbytes v ++ encodeByte x.val)
      · split
        · apply spec_bind (push_spec' v 126#u8 (by omega))
          rintro w1 ⟨hw1, hl1⟩
          apply spec_mono (push_spec' w1 49#u8 (by omega))
          rintro w2 ⟨hw2, _⟩
          rw [hw2, hw1]; simp [encodeByte]
        · apply spec_bind (push_spec' v 126#u8 (by omega))
          rintro w1 ⟨hw1, hl1⟩
          apply spec_mono (push_spec' w1 48#u8 (by omega))
          rintro w2 ⟨hw2, _⟩
          rw [hw2, hw1]; simp [encodeByte]
        · rename_i h47 h126
          apply spec_mono (push_spec' v x (by omega))
          rintro w ⟨hw, _⟩
          have n47 : x.val ≠ 47 := by simpa using val_ne_of_ne h47
          have n126 : x.val ≠ 126 := by simpa using val_ne_of_ne h126
          rw [hw]; simp [encodeByte, n47, n126]
      · intro w hw
        step as ⟨k', hk''⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hk'', hstep, hw, hv]
    next hge =>
      apply (spec_ok _).mpr
      have : k.val = (bytes s).length := by scalar_tac
      show vbytes v = encode (bytes s)
      rw [hv, this, List.take_length]
  · exact ⟨hi, hv⟩

theorem decodeLoop_spec (e : Slice U8) (hb : 2 * e.length + 1 ≤ Usize.max) (R : List Nat)
    (v : alloc.vec.Vec U8) (esc : Bool) (i : Usize)
    (hi : i.val ≤ e.length) (hv : vbytes v ++ Model.decLoop esc ((bytes e).drop i.val) = R)
    (hvl : v.length ≤ i.val) :
    jsonptr.token.decoded_adapted_loop e v esc i ⦃ w => vbytes w = R ⦄ := by
  have hlen : (bytes e).length = e.length := bytes_length e
  unfold jsonptr.token.decoded_adapted_loop
  apply loop.spec_decr_nat (fun st : alloc.vec.Vec U8 × Bool × Usize => e.length - st.2.2.val)
    (fun st => st.2.2.val ≤ e.length ∧
      vbytes st.1 ++ Model.decLoop st.2.1 ((bytes e).drop st.2.2.val) = R ∧ st.1.length ≤ st.2.2.val)
  · rintro ⟨v, esc, k⟩ ⟨hk, hv, hvl⟩
    simp only at hk hv hvl
    simp only [jsonptr.token.decoded_adapted_loop.body]
    split
    next hlt =>
      have hk' : k.val < e.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec e k hk')
      intro x hx
      have hL := bytes_getElem? e hk' hx
      have hd := Model.drop_cons hL
      rw [hd] at hv
      clear hx hd
      apply spec_bind (Pₘ := fun (p : alloc.vec.Vec U8 × Bool) =>
        vbytes p.1 ++ Model.decLoop p.2 ((bytes e).drop (k.val + 1)) = R ∧ p.1.length ≤ v.length + 1)
      · split
        · apply (spec_ok _).mpr
          refine ⟨?_, by simp only; omega⟩
          rw [← hv]; simp [Model.decLoop]
        · split <;> rename_i hesc
          · apply spec_bind (push_spec' v 126#u8 (by omega))
            rintro w ⟨hw, hwl⟩
            apply (spec_ok _).mpr
            refine ⟨?_, by simp only; omega⟩
            rw [← hv, hw]; simp [Model.decLoop, hesc]
          · apply spec_bind (push_spec' v _ (by omega))
            rintro w ⟨hw, hwl⟩
            apply (spec_ok _).mpr
            refine ⟨?_, by simp only; omega⟩
            rw [← hv, hw]; simp [Model.decLoop, hesc]
        · split <;> rename_i hesc
          · apply spec_bind (push_spec' v 47#u8 (by omega))
            rintro w ⟨hw, hwl⟩
            apply (spec_ok _).mpr
            refine ⟨?_, by simp only; omega⟩
            rw [← hv, hw]; simp [Model.decLoop, hesc]
          · apply spec_bind (push_spec' v _ (by omega))
            rintro w ⟨hw, hwl⟩
            apply (spec_ok _).mpr
            refine ⟨?_, by simp only; omega⟩
            rw [← hv, hw]; simp [Model.decLoop, hesc]
        · rename_i h126 h48 h49
          have n126 : x.val ≠ 126 := by simpa using val_ne_of_ne h126
          have n48 : x.val ≠ 48 := by simpa using val_ne_of_ne h48
          have n49 : x.val ≠ 49 := by simpa using val_ne_of_ne h49
          apply spec_bind (push_spec' v x (by omega))
          rintro w ⟨hw, hwl⟩
          apply (spec_ok _).mpr
          refine ⟨?_, by simp only; omega⟩
          rw [← hv, hw]; simp [Model.decLoop, n126, n48, n49]
      · rintro ⟨w, esc'⟩ ⟨hw, hwl⟩
        step as ⟨k', hk''⟩
        refine ⟨by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hk'']; exact hw
        · simp only at hwl ⊢; scalar_tac
    next hge =>
      apply (spec_ok _).mpr
      have : k.val = (bytes e).length := by scalar_tac
      show vbytes v = R
      rw [← hv, this, List.drop_length]; simp [Model.decLoop]
  · exact ⟨hi, hv, hvl⟩

theorem mem_take_bytes (s : Slice U8) (i : Nat) (b : Nat) (hb : b ∈ (bytes s).take i) :
    ∃ k y, k < i ∧ s.val[k]? = some y ∧ y.val = b := by
  rw [bytes, ← List.map_take] at hb
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hy
  have hki : k < i := by
    have := (List.getElem?_eq_some_iff.mp hk).1; simp at this; omega
  rw [List.getElem?_take, if_pos hki] at hk
  exact ⟨k, y, hki, hk, rfl⟩

theorem mem_bytes (s : Slice U8) (b : Nat) (hb : b ∈ bytes s) :
    ∃ (k : Nat) (y : U8), s.val[k]? = some y ∧ y.val = b := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hy
  exact ⟨k, y, hk, rfl⟩

/-- Target 2, `Token::new` then `encoded`. -/
theorem newAdapted : EncodeContract := by
  intro x hbound
  have hb := sliceBound_le hbound
  apply ok_of_spec
  unfold jsonptr.token.new_adapted
  apply spec_bind (slashTilde_spec x)
  intro o ho
  cases o with
  | none =>
    apply (spec_ok _).mpr
    have hall : ∀ b ∈ bytes x, b ≠ 47 ∧ b ≠ 126 := by
      intro b hb'
      obtain ⟨k, y, hk, rfl⟩ := mem_bytes x b hb'
      have := ho k y hk
      constructor <;> intro hv <;> apply this
      · left; apply UScalar.eq_of_val_eq; simp [hv]
      · right; apply UScalar.eq_of_val_eq; simp [hv]
    exact ⟨(Model.needsNoEncoding_iff _).mpr hall, Model.encode_eq_self _ hall⟩
  | some i =>
    obtain ⟨⟨c, hc, hc'⟩, hpre⟩ := ho
    have hi : i.val < x.length := (List.getElem?_eq_some_iff.mp hc).1
    simp only
    step as ⟨n1, hn1⟩
    apply spec_bind (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec _ x
      (by simp only; omega))
    rintro s1 ⟨hs1, hs1l⟩
    obtain ⟨v1, hv1, hv1'⟩ := extend_ok (alloc.vec.Vec.with_capacity U8 n1) s1
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length, alloc.vec.Vec.new] at hs1l ⊢; try omega)
    rw [hv1]
    simp only [bind_ok]
    have hpref : ∀ b ∈ (bytes x).take i.val, b ≠ 47 ∧ b ≠ 126 := by
      intro b hb'
      obtain ⟨k, y, hk, hy, rfl⟩ := mem_take_bytes x i.val b hb'
      have := hpre k y hk hy
      constructor <;> intro hv <;> apply this
      · left; apply UScalar.eq_of_val_eq; simp [hv]
      · right; apply UScalar.eq_of_val_eq; simp [hv]
    have hv1b : vbytes v1 = encode ((bytes x).take i.val) := by
      rw [Model.encode_eq_self _ hpref]
      simp [vbytes, hv1', hs1, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, bytes, List.map_take]
    apply spec_bind (encodeLoop_spec x hb v1 i (by omega) hv1b)
    intro v2 hv2
    apply (spec_ok _).mpr
    refine ⟨?_, hv2⟩
    cases hn : needsNoEncoding (bytes x)
    · rfl
    · exfalso
      have hall := (Model.needsNoEncoding_iff _).mp hn
      have hmem : c.val ∈ bytes x := by
        simp only [bytes]; exact List.mem_map.mpr ⟨c, List.mem_of_getElem? hc, rfl⟩
      have := hall c.val hmem
      rcases hc' with rfl | rfl <;> simp at this

theorem bytes_getElem?_iff (s : Slice U8) (k n : Nat) (h : (bytes s)[k]? = some n) :
    ∃ y, s.val[k]? = some y ∧ y.val = n := by
  simp only [bytes, List.getElem?_map] at h
  cases hy : s.val[k]? with
  | none => simp [hy] at h
  | some y => simp [hy] at h; exact ⟨y, rfl, h⟩

/-- Target 3, `Token::decoded`. -/
theorem decodedAdapted : DecodeContract := by
  intro e hbound
  have hb := sliceBound_le hbound
  apply ok_of_spec
  unfold jsonptr.token.decoded_adapted
  apply spec_bind (tilde_spec e)
  intro o ho
  cases o with
  | none =>
    apply (spec_ok _).mpr
    have hno : 126 ∉ bytes e := by
      intro hm
      obtain ⟨k, y, hk, hy⟩ := mem_bytes e 126 hm
      exact ho k y hk (UScalar.eq_of_val_eq (by simp [hy]))
    exact ⟨hno, fun x hx => Model.encode_noTilde x _ hx hno⟩
  | some i =>
    obtain ⟨⟨c, hc, hc'⟩, hpre⟩ := ho
    have hi : i.val < e.length := (List.getElem?_eq_some_iff.mp hc).1
    simp only
    step as ⟨n1, hn1⟩
    apply spec_bind (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec _ e
      (by simp only; omega))
    rintro s1 ⟨hs1, hs1l⟩
    obtain ⟨v1, hv1, hv1'⟩ := extend_ok (alloc.vec.Vec.with_capacity U8 n1) s1
      (by simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.length, alloc.vec.Vec.new] at hs1l ⊢; try omega)
    rw [hv1]
    simp only [bind_ok]
    step as ⟨i3, hi3⟩
    have hv1b : vbytes v1 = (bytes e).take i.val := by
      simp [vbytes, hv1', hs1, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, bytes, List.map_take]
    have hci : (bytes e)[i.val]? = some 126 := by
      simp [bytes, hc, hc']
    apply spec_bind (decodeLoop_spec e hb ((bytes e).take i.val ++ Model.decLoop true ((bytes e).drop (i.val + 1)))
      v1 true i3 (by omega) (by rw [hv1b, hi3]) (by
        have h1 := vbytes_length v1
        rw [hv1b, List.length_take, bytes_length] at h1
        omega))
    intro v2 hv2
    apply (spec_ok _).mpr
    refine ⟨List.mem_of_getElem? hci, ?_⟩
    intro x hx
    rw [hv2]
    have key := Model.decode_firstTilde x i.val (by rw [hx]; exact hci) (by
      rw [hx]
      intro k n hk hn hn126
      obtain ⟨y, hy, hyv⟩ := bytes_getElem?_iff e k n hn
      exact hpre k y hk hy (UScalar.eq_of_val_eq (by simp [hyv, hn126])))
    rw [hx] at key
    exact key.symm

end JsonptrAdaptedProofs
