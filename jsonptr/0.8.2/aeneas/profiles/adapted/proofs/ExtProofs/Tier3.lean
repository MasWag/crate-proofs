import Statements.Tier3Buf
import ExtProofs.Tier2Refute

/-!
# Tier 3 proofs (specification sections 12-14), implementation agent

Parse wrappers and `is_next` are proved as compositions over the target 1 and
target 5 contracts (`ValidateContract`, `IndexContract`), which the other
implementation agent proves; they close once those proofs are merged.
-/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

theorem vbytes_val (v : alloc.vec.Vec U8) : vbytes v = v.val.map (fun b => b.val) := rfl

theorem vbytes_len (v : alloc.vec.Vec U8) : (vbytes v).length = v.length := by simp [vbytes]

theorem extend_spec (v : alloc.vec.Vec U8) (s : Slice U8) (h : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s ⦃ w => vbytes w = vbytes v ++ bytes s ⦄ := by
  obtain ⟨l, hl, hlv⟩ := ok_of_spec (List.clone_spec (clone := core.clone.CloneU8.clone) (l := s.val)
    (fun x _ => rfl))
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos h]
  simp only [hl, bind_tc_ok, bind_ok, spec_ok]
  simp [vbytes, bytes, alloc.vec.Vec.from_val, hlv.1]

theorem copy_spec (s : Slice U8) :
    jsonptr.adapted_api.copy_bytes_ext s ⦃ v => vbytes v = bytes s ⦄ := by
  unfold jsonptr.adapted_api.copy_bytes_ext
  apply spec_mono (extend_spec _ s (by simp))
  intro w hw; simpa [vbytes] using hw

theorem push_spec (v : alloc.vec.Vec U8) (x : U8) (h : v.length < Usize.max) :
    alloc.vec.Vec.push v x ⦃ w => vbytes w = vbytes v ++ [x.val] ⦄ := by
  apply spec_mono (alloc.vec.Vec.push_spec v x h)
  intro w hw; simp [vbytes, hw]

/-- Every encoded token satisfies the pointer-token invariant. -/
theorem tokOK_of_valid (t : List Nat) (h : ValidEncodedToken t) : TokOK t := by
  obtain ⟨x, rfl⟩ := h
  induction x with
  | nil => exact ⟨by simp [encode], noBad_nil⟩
  | cons b x ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [encode]
    by_cases h47 : b = 47
    · subst h47
      refine ⟨by simp [encodeByte, h1], ?_⟩
      have he : encodeByte 47 = [126, 49] := by decide
      rw [he, List.cons_append, List.cons_append, List.nil_append, noBad_cons, noBad_cons]
      exact ⟨fun _ => Or.inr rfl, fun h => absurd h (by decide), h2⟩
    · by_cases h126 : b = 126
      · subst h126
        refine ⟨by simp [encodeByte, h1], ?_⟩
        have he : encodeByte 126 = [126, 48] := by decide
        rw [he, List.cons_append, List.cons_append, List.nil_append, noBad_cons, noBad_cons]
        exact ⟨fun _ => Or.inl rfl, fun h => absurd h (by decide), h2⟩
      · refine ⟨by simp [encodeByte, h47, h126, h1]; try exact fun e => h47 e.symm, ?_⟩
        simp only [encodeByte, h47, h126, ↓reduceIte, List.cons_append, List.nil_append]
        rw [noBad_cons]; exact ⟨fun h => absurd h h126, h2⟩

theorem validPointer_append (X O : List Nat) (hX : ValidPointer X) (hO : ValidPointer O) :
    ValidPointer (X ++ O) := by
  rw [← render_tokens_of_valid X hX, ← render_tokens_of_valid O hO, ← renderEncoded_append]
  apply validPointer_of_tokOK
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact tokOK_of_validPointer _ hX t h
  · exact tokOK_of_validPointer _ hO t h

theorem validPointer_slash_tok (t : List Nat) (ht : ValidEncodedToken t) : ValidPointer (47 :: t) := by
  have := validPointer_of_tokOK [t] (by simpa using tokOK_of_valid t ht)
  simpa [renderEncoded] using this

theorem isize_le_usize (n : Nat) (h : (n : Int) ≤ Isize.max) : n < Usize.max := by
  have : (2 * Isize.max + 1 : Int) = Usize.max := by
    rw [Isize.max_def, Usize.max_def, Isize.numBits_def, Usize.numBits_def]
    simp only [IScalarTy.Isize_numBits_eq, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  have : (0 : Int) ≤ Isize.max := by scalar_tac
  omega

/-! ## Section 12 -/

theorem bufNewAdapted : BufNewContract :=
  ⟨_, rfl, by simp [vbytes], (validPointer_iff []).mpr ⟨Or.inl rfl, noBad_nil⟩⟩

theorem toBufAdapted : ToBufContract := by
  intro xs hv
  obtain ⟨v, hv1, hv2⟩ := ok_of_spec (copy_spec xs)
  exact ⟨v, hv1, hv2, by rw [hv2]; exact hv⟩

theorem clearAdapted : ClearContract := fun _ => ⟨_, rfl, by simp [vbytes]⟩

theorem pushBack_spec (buf : alloc.vec.Vec U8) (t : Slice U8)
    (hb : LenBound (pushBack (vbytes buf) (bytes t))) :
    jsonptr.adapted_api.push_back_adapted buf t ⦃ v => vbytes v = pushBack (vbytes buf) (bytes t) ⦄ := by
  have hl := isize_le_usize _ hb
  simp [pushBack, vbytes_len] at hl
  unfold jsonptr.adapted_api.push_back_adapted
  apply spec_bind (push_spec buf 47#u8 (by scalar_tac))
  intro b1 hb1
  have hlen : b1.length = buf.length + 1 := by rw [← vbytes_len, hb1]; simp [vbytes_len]
  apply spec_mono (extend_spec b1 t (by rw [hlen]; scalar_tac))
  intro w hw; rw [hw, hb1]; simp [pushBack]

theorem pushBackAdapted : PushBackContract := by
  intro buf t hv ht hb
  obtain ⟨v, h1, h2⟩ := ok_of_spec (pushBack_spec buf t hb)
  refine ⟨v, h1, h2, ?_⟩
  rw [h2, pushBack]; exact validPointer_append _ _ hv (validPointer_slash_tok _ ht)

theorem pushFront_spec (buf : alloc.vec.Vec U8) (t : Slice U8)
    (hb : LenBound (pushFront (vbytes buf) (bytes t))) :
    jsonptr.adapted_api.push_front_adapted buf t ⦃ v => vbytes v = pushFront (vbytes buf) (bytes t) ⦄ := by
  have hl := isize_le_usize _ hb
  simp [pushFront, vbytes_len] at hl
  unfold jsonptr.adapted_api.push_front_adapted
  apply spec_bind (push_spec (alloc.vec.Vec.new U8) 47#u8 (by simp; scalar_tac))
  intro b1 hb1
  have hlen : b1.length = 1 := by rw [← vbytes_len, hb1]; simp [vbytes]
  apply spec_bind (extend_spec b1 t (by rw [hlen]; scalar_tac))
  intro b2 hb2
  have hlen2 : b2.length = 1 + t.length := by rw [← vbytes_len, hb2]; simp [vbytes_len, hlen]
  apply spec_mono (extend_spec b2 (alloc.vec.Vec.deref buf) (by simp [alloc.vec.Vec.deref]; scalar_tac))
  intro w hw; rw [hw, hb2, hb1]; simp [pushFront, vbytes, bytes, alloc.vec.Vec.deref]

theorem pushFrontAdapted : PushFrontContract := by
  intro buf t hv ht hb
  obtain ⟨v, h1, h2⟩ := ok_of_spec (pushFront_spec buf t hb)
  refine ⟨v, h1, h2, ?_⟩
  rw [h2, pushFront]
  have := validPointer_append _ _ (validPointer_slash_tok _ ht) hv
  simpa using this

theorem append_spec (buf : alloc.vec.Vec U8) (o : Slice U8)
    (hb : LenBound (append (vbytes buf) (bytes o))) :
    jsonptr.adapted_api.append_adapted buf o ⦃ v => vbytes v = append (vbytes buf) (bytes o) ⦄ := by
  have hl := isize_le_usize _ hb
  simp [append, vbytes_len] at hl
  simp only [jsonptr.adapted_api.append_adapted]
  split
  next h0 =>
    have : vbytes buf = [] := by
      have : buf.length = 0 := by scalar_tac
      simpa [vbytes] using this
    apply spec_mono (copy_spec o); intro w hw; simp [append, this, hw]
  next h0 =>
    step as ⟨b, hb'⟩
    split
    next he =>
      have : bytes o = [] := by
        have : o.length = 0 := by simpa [hb'] using he
        simpa [bytes] using this
      simp [append, this]
    next he =>
      apply spec_mono (extend_spec buf o (by scalar_tac))
      intro w hw; simp [append, hw]

theorem appendAdapted : AppendContract := by
  intro buf o hv ho hb
  obtain ⟨v, h1, h2⟩ := ok_of_spec (append_spec buf o hb)
  exact ⟨v, h1, h2, by rw [h2, append]; exact validPointer_append _ _ hv ho⟩

theorem withTrailingTokenAdapted : WithTrailingTokenContract := by
  intro xs t hv ht hb
  apply ok_of_spec
  unfold jsonptr.adapted_api.with_trailing_token_adapted jsonptr.adapted_api.to_buf_adapted
  apply spec_bind (copy_spec xs)
  intro v hv'
  rw [← hv'] at hb
  apply spec_mono (pushBack_spec v t hb)
  intro w hw
  rw [hw, hv']
  exact ⟨rfl, validPointer_append _ _ hv (validPointer_slash_tok _ ht)⟩

theorem withLeadingTokenAdapted : WithLeadingTokenContract := by
  intro xs t hv ht hb
  apply ok_of_spec
  unfold jsonptr.adapted_api.with_leading_token_adapted jsonptr.adapted_api.to_buf_adapted
  apply spec_bind (copy_spec xs)
  intro v hv'
  rw [← hv'] at hb
  apply spec_mono (pushFront_spec v t hb)
  intro w hw
  rw [hw, hv']
  refine ⟨rfl, ?_⟩
  have := validPointer_append _ _ (validPointer_slash_tok _ ht) hv
  simpa [pushFront] using this

theorem concatAdapted : ConcatContract := by
  intro xs o hv ho hb
  apply ok_of_spec
  unfold jsonptr.adapted_api.concat_adapted jsonptr.adapted_api.to_buf_adapted
  apply spec_bind (copy_spec xs)
  intro v hv'
  rw [← hv'] at hb
  apply spec_mono (append_spec v o hb)
  intro w hw
  rw [hw, hv']
  exact ⟨rfl, validPointer_append _ _ hv ho⟩

/-! ## Section 14 -/

theorem tokenEncodedAdapted : TokenEncodedContract := fun t ht => ⟨t, rfl, rfl, ht⟩

theorem tokenToOwnedAdapted : TokenToOwnedContract := by
  intro t ht
  obtain ⟨v, h1, h2⟩ := ok_of_spec (copy_spec t)
  exact ⟨v, h1, h2, by rw [h2]; exact ht⟩

theorem sotStringAdapted : SotStringContract := by
  intro v
  exact ⟨_, _, rfl, rfl, by simp [bytes, vbytes, alloc.vec.Vec.deref]⟩

theorem sotTokenAdapted : SotTokenContract := by
  intro v _
  exact ⟨_, _, rfl, rfl, by simp [bytes, vbytes, alloc.vec.Vec.deref]⟩

theorem parseIndex_next_iff (s : List Nat) : parseIndex Usize.max s = .ok .next ↔ s = [45] := by
  constructor
  · intro h
    unfold parseIndex at h
    split at h
    · assumption
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h <;> cases h
  · intro h; simp [parseIndex, h]

theorem isNextAdapted (hidx : IndexContract) : IsNextContract := by
  intro t _
  obtain ⟨r, hr, hm⟩ := hidx t
  have hdash := parseIndex_next_iff (bytes t)
  cases r with
  | Ok i =>
    cases i with
    | Num n =>
      refine ⟨false, by simp [jsonptr.adapted_api.is_next_adapted, hr], ?_⟩
      simp only [indexOutcome, index] at hm
      simp only [isNext]
      symm; rw [decide_eq_false_iff_not]; intro h; rw [← hdash] at h; rw [h] at hm; cases hm
    | Next =>
      refine ⟨true, by simp [jsonptr.adapted_api.is_next_adapted, hr], ?_⟩
      simp only [indexOutcome, index] at hm
      simp only [isNext]; symm; rw [decide_eq_true_eq]; exact hdash.mp hm.symm
  | Err e =>
    refine ⟨false, by simp [jsonptr.adapted_api.is_next_adapted, hr], ?_⟩
    simp only [indexOutcome] at hm
    simp only [isNext]
    symm; rw [decide_eq_false_iff_not]; intro h; rw [← hdash] at h; rw [h] at hm; cases hm

/-! ## Section 13 (composed with target 1) -/

theorem pointerParseAdapted (hval : ValidateContract) : PointerParseContract := by
  intro s
  obtain ⟨r, hr, hm, hok⟩ := hval s
  cases r with
  | Ok v =>
    refine ⟨.Ok v, by simp [jsonptr.adapted_api.pointer_parse_adapted, hr], ?_, ?_⟩
    · rw [hok v rfl]
    · simpa [ptrOutcome] using hm.symm
  | Err e => exact ⟨.Err e, by simp [jsonptr.adapted_api.pointer_parse_adapted, hr], hm⟩

theorem deref_bytes (s : alloc.vec.Vec U8) : bytes (alloc.vec.Vec.deref s) = vbytes s := by
  simp [bytes, vbytes, alloc.vec.Vec.deref]

theorem bufTryFromStringAdapted (hval : ValidateContract) : BufTryFromStringContract := by
  intro s
  obtain ⟨r, hr, hm, _⟩ := hval (alloc.vec.Vec.deref s)
  rw [deref_bytes] at hm
  cases r with
  | Ok v => exact ⟨.Ok s, by simp [jsonptr.adapted_api.buf_try_from_string_adapted, hr], rfl,
      by simpa [ptrOutcome] using hm.symm⟩
  | Err e => exact ⟨.Err e, by simp [jsonptr.adapted_api.buf_try_from_string_adapted, hr], hm⟩

theorem bufParseAdapted (hval : ValidateContract) : BufParseContract := by
  intro s
  obtain ⟨r, hr, hm, _⟩ := hval (alloc.vec.Vec.deref s)
  rw [deref_bytes] at hm
  cases r with
  | Ok v => exact ⟨.Ok s, by simp [jsonptr.adapted_api.buf_parse_adapted, hr], rfl,
      by simpa [ptrOutcome] using hm.symm⟩
  | Err e => exact ⟨.Err { source := e, subject := s },
      by simp [jsonptr.adapted_api.buf_parse_adapted, hr], hm, rfl⟩

theorem bufTryFromStrAdapted (hval : ValidateContract) : BufTryFromStrContract := by
  intro s
  obtain ⟨r, hr, hm⟩ := pointerParseAdapted hval s
  cases r with
  | Ok p =>
    obtain ⟨hpb, hpe⟩ := hm
    obtain ⟨v, hv1, hv2⟩ := ok_of_spec (copy_spec p)
    refine ⟨.Ok v, by simp [jsonptr.adapted_api.buf_try_from_str_adapted, jsonptr.adapted_api.to_buf_adapted,
      hr, hv1], by rw [hv2, hpb], hpe⟩
  | Err e => exact ⟨.Err e, by simp [jsonptr.adapted_api.buf_try_from_str_adapted, hr], hm⟩

theorem fromStaticAdapted (hval : ValidateContract) : FromStaticContract := by
  intro s
  obtain ⟨r, hr, hm, _⟩ := hval s
  constructor
  · intro hn
    cases r with
    | Ok _ => simp [jsonptr.adapted_api.from_static_adapted, jsonptr.adapted_api.validate_is_ok_adapted, hr, massert]
    | Err e =>
      cases e with
      | NoLeadingSlash => simp [ptrOutcome, hn] at hm
      | InvalidEncoding d src =>
        obtain ⟨t, src⟩ := src
        cases src <;> simp [ptrOutcome, hn] at hm
  · intro hn
    cases r with
    | Ok _ => simp [ptrOutcome] at hm; exact absurd hm.symm hn
    | Err e => simp [jsonptr.adapted_api.from_static_adapted, jsonptr.adapted_api.validate_is_ok_adapted, hr, massert]

/-! ## pop_back, pop_front -/

theorem splitBack_model (X : List Nat) (hv : ValidPointer X) (i : Nat) (h47 : X[i]? = some 47)
    (hlast : ∀ k, i < k → X[k]? ≠ some 47) :
    splitBack X = some (X.take i, X.drop (i + 1)) := by
  obtain ⟨htok, hvh, _⟩ := lastSlash_model X hv i h47 hlast
  simp only [splitBack, htok, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    List.dropLast_concat]
  rw [render_tokens_of_valid _ hvh]

theorem popBackAdapted : PopBackContract := by
  intro buf hv
  have hd : bytes (alloc.vec.Vec.deref buf) = vbytes buf := deref_bytes buf
  apply (fun h => by obtain ⟨⟨r, v⟩, h1, h2⟩ := ok_of_spec h; exact ⟨r, v, h1, h2⟩ :
    jsonptr.adapted_api.pop_back_adapted buf ⦃ p => (vbytes p.2, ovbytes p.1) = popBack (vbytes buf) ∧
      ValidPointer (vbytes p.2) ∧ ValidTokOpt (ovbytes p.1) ⦄ → _)
  unfold jsonptr.adapted_api.pop_back_adapted
  apply spec_bind (rfindSlash_spec (alloc.vec.Vec.deref buf))
  intro o ho
  rw [hd] at ho
  cases o with
  | none =>
    have hnil := valid_noSlash_nil _ hv ho
    apply (spec_ok _).mpr
    refine ⟨by simp [popBack, splitBack, hnil, encodedTokens_nil, ovbytes], hv, by simp [ValidTokOpt, ovbytes]⟩
  | some i =>
    obtain ⟨hi, h47, hlast⟩ := ho
    have hilen : i.val < buf.length := by simpa [alloc.vec.Vec.deref] using hi
    have hsb := splitBack_model _ hv i.val h47 hlast
    obtain ⟨htok, hvh, hns⟩ := lastSlash_model _ hv i.val h47 hlast
    step as ⟨i1, hi1⟩
    step as ⟨s1, hs1, _⟩
    apply spec_bind (copy_spec s1); intro v hv1
    step as ⟨s2, hs2, _⟩
    apply spec_bind (copy_spec s2); intro v1 hv2
    have hv1len : v1.length = i.val + 1 := by
      rw [← vbytes_len, hv2]; simp [hs2, bytes, List.slice]; scalar_tac
    step as ⟨i3, hi3⟩
    step as ⟨s3, hs3, _⟩
    apply spec_bind (copy_spec s3); intro b1 hb1
    apply (spec_ok _).mpr
    have hbv : vbytes v = (vbytes buf).drop (i.val + 1) := by
      rw [hv1]; simp [bytes, vbytes, hs1, List.map_drop, hi1]
    have hbb : vbytes b1 = (vbytes buf).take i.val := by
      rw [hb1]
      have : bytes s3 = (bytes s2).take i.val := by
        have hv2' : s3.val.map (fun b => b.val) = (v1.val.map (fun b => b.val)).take i3.val := by
          simp [hs3, List.slice, List.map_take]
        simp only [bytes]; rw [hv2']
        rw [show (v1.val.map fun b => b.val) = vbytes v1 from rfl, hv2]
        congr 1; scalar_tac
      rw [this]; simp [bytes, vbytes, hs2, List.slice, List.map_take, hi1]
      rw [List.take_take]; congr 1; omega
    refine ⟨by simp [popBack, hsb, hbv, hbb, ovbytes], by rw [hbb]; exact hvh, ?_⟩
    intro t ht; simp [ovbytes] at ht; rw [← ht, hbv]
    exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok]; simp)

theorem popFrontAdapted : PopFrontContract := by
  intro buf hv
  apply (fun h => by obtain ⟨⟨r, v⟩, h1, h2⟩ := ok_of_spec h; exact ⟨r, v, h1, h2⟩ :
    jsonptr.adapted_api.pop_front_adapted buf ⦃ p => (vbytes p.2, ovbytes p.1) = popFront (vbytes buf) ∧
      ValidPointer (vbytes p.2) ∧ ValidTokOpt (ovbytes p.1) ⦄ → _)
  simp only [jsonptr.adapted_api.pop_front_adapted]
  split
  next h0 =>
    have hnil : vbytes buf = [] := by
      have : buf.length = 0 := by scalar_tac
      simpa [vbytes] using this
    apply (spec_ok _).mpr
    refine ⟨by simp [popFront, splitFront, hnil, encodedTokens_nil, ovbytes], hv, by simp [ValidTokOpt, ovbytes]⟩
  next h0 =>
    have hlen : 1 ≤ buf.length := by
      have : buf.length ≠ 0 := by intro h; apply h0; scalar_tac
      omega
    obtain ⟨r, hr⟩ : ∃ r, vbytes buf = 47 :: r := by
      rcases slashLed_of_valid _ hv with h | h
      · have h0' : (vbytes buf).length = 0 := by rw [h]; rfl
        rw [vbytes_len] at h0'; omega
      · cases hx : vbytes buf with
        | nil => rw [hx] at h; simp at h
        | cons x r => rw [hx] at h; simp at h; exact ⟨r, by rw [h]⟩
    step as ⟨s, hs, _⟩
    have hbs : bytes s = r := by
      have : bytes s = (vbytes buf).drop 1 := by simp [bytes, vbytes, hs, List.map_drop]
      rw [this, hr]; rfl
    apply spec_bind (findSlash_spec s)
    intro o ho
    cases o with
    | none =>
      have hns : 47 ∉ r := hbs ▸ ho
      have htok : encodedTokens (vbytes buf) = [r] := by
        rw [hr, encodedTokens_slash, splitSlash_noSlash r hns]
      simp only []
      apply spec_bind (Pₘ := fun p : alloc.vec.Vec U8 × alloc.vec.Vec U8 => vbytes p.1 = [] ∧ vbytes p.2 = vbytes buf)
      · apply spec_bind (show alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFullSlice U8) buf () ⦃
            fun s1 => bytes s1 = vbytes buf ⦄ by
          simp [alloc.vec.Vec.index, core.slice.index.Slice.index, bytes, vbytes]; rfl)
        intro s1 hs1; apply spec_bind (copy_spec s1); intro v1 hv1
        apply (spec_ok _).mpr; exact ⟨by simp [vbytes], by rw [hv1, hs1]⟩
      · rintro ⟨b1, v⟩ ⟨hb1, hvv⟩
        have hvl : 1 ≤ v.length := by rw [← vbytes_len, hvv, vbytes_len]; exact hlen
        step as ⟨s1, hs1, _⟩
        apply spec_bind (copy_spec s1); intro v1 hv1
        apply (spec_ok _).mpr
        have hb : vbytes v1 = r := by
          rw [hv1]; simp only [bytes, hs1, List.map_drop]
          rw [show v.val.map (fun b => b.val) = vbytes v from rfl, hvv, hr]; rfl
        refine ⟨by simp [popFront, splitFront, htok, hb, hb1, ovbytes, renderEncoded], ?_, ?_⟩
        · rw [hb1]; exact (validPointer_iff []).mpr ⟨Or.inl rfl, noBad_nil⟩
        · intro t ht; simp [ovbytes] at ht; rw [← ht, hb]
          exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok]; simp)
    | some j =>
      obtain ⟨hj, hj47, hfirst⟩ := ho
      rw [hbs] at hj47 hfirst
      have hd := decomp_at r j.val hj47
      have hns := noSlash_before r j.val hfirst
      have htok : encodedTokens (vbytes buf) = r.take j.val :: encodedTokens (47 :: r.drop (j.val + 1)) := by
        rw [hr]; conv_lhs => rw [hd]
        exact encodedTokens_cons_split _ _ hns (Or.inr rfl)
      have hrest : renderEncoded (encodedTokens (47 :: r.drop (j.val + 1))) = 47 :: r.drop (j.val + 1) :=
        renderEncoded_encodedTokens _ (Or.inr rfl)
      have hjl : j.val < r.length := (List.getElem?_eq_some_iff.mp hj47).1
      have hbl : (vbytes buf).length = r.length + 1 := by rw [hr]; simp
      rw [vbytes_len] at hbl
      simp only []
      apply spec_bind (Pₘ := fun p : alloc.vec.Vec U8 × alloc.vec.Vec U8 =>
        vbytes p.1 = (vbytes buf).drop (j.val + 1) ∧ vbytes p.2 = (vbytes buf).take (j.val + 1))
      · step as ⟨i2, hi2⟩
        step as ⟨s1, hs1, _⟩
        apply spec_bind (copy_spec s1); intro b2 hb2
        step as ⟨s2, hs2, _⟩
        apply spec_bind (copy_spec s2); intro v1 hv1
        apply (spec_ok _).mpr
        refine ⟨by rw [hb2]; simp [bytes, vbytes, hs1, List.map_drop, hi2], ?_⟩
        rw [hv1]; simp [bytes, vbytes, hs2, List.slice, List.map_take, hi2]
      · rintro ⟨b1, v⟩ ⟨hb1, hvv⟩
        have hvl : 1 ≤ v.length := by rw [← vbytes_len, hvv, List.length_take, vbytes_len]; omega
        step as ⟨s1, hs1, _⟩
        apply spec_bind (copy_spec s1); intro v1 hv1
        apply (spec_ok _).mpr
        have hb : vbytes v1 = r.take j.val := by
          rw [hv1]; simp only [bytes, hs1, List.map_drop]
          rw [show v.val.map (fun b => b.val) = vbytes v from rfl, hvv, hr]; simp
        have hb1' : vbytes b1 = 47 :: r.drop (j.val + 1) := by
          rw [hb1, hr]; simp
          rw [List.drop_eq_getElem_cons (by omega)]
          congr 1
          rw [List.getElem?_eq_getElem hjl] at hj47; simpa using hj47
        refine ⟨by simp [popFront, splitFront, htok, hb, hb1', ovbytes, hrest], ?_, ?_⟩
        · rw [hb1']
          have hvd := valid_split ((47 :: r).take (j.val + 1)) ((47 :: r).drop (j.val + 1))
            (by rw [List.take_append_drop, ← hr]; exact hv)
          have : (47 :: r).drop (j.val + 1) = 47 :: r.drop (j.val + 1) := by
            simp; rw [List.drop_eq_getElem_cons hjl]; congr 1
            rw [List.getElem?_eq_getElem hjl] at hj47; simpa using hj47
          rw [this] at hvd
          exact (hvd (Or.inr rfl)).2
        · intro t ht; simp [ovbytes] at ht; rw [← ht, hb]
          exact validEncodedToken_of_valid_mem _ _ hv (by rw [htok]; simp)

/-! ## from_tokens -/

theorem renderEncoded_length_take_le (ts : List (List Nat)) (k : Nat) :
    (renderEncoded (ts.take k)).length ≤ (renderEncoded ts).length := by
  conv_rhs => rw [← List.take_append_drop k ts, renderEncoded_append]
  simp

theorem fromTokensAdapted : FromTokensContract := by
  intro ts hts hb
  have hl := isize_le_usize _ hb
  set L := ts.val.map vbytes with hL
  apply ok_of_spec
  unfold jsonptr.adapted_api.from_tokens_adapted jsonptr.adapted_api.from_tokens_adapted_loop
  apply loop.spec_decr_nat (fun p : alloc.vec.Vec U8 × Usize => ts.length - p.2.val)
    (fun p => p.2.val ≤ ts.length ∧ vbytes p.1 = renderEncoded (L.take p.2.val))
  · rintro ⟨v, i⟩ ⟨hi, hv⟩
    simp only at hi hv
    simp only [jsonptr.adapted_api.from_tokens_adapted_loop.body]
    split
    next hlt =>
      have hil : i.val < ts.length := by scalar_tac
      have hti : L[i.val]? = some (vbytes ts.val[i.val]) := by
        simp [hL, List.getElem?_map, List.getElem?_eq_getElem hil]
      have hsucc := renderEncoded_take_succ L i.val _ hti
      have hle := renderEncoded_length_take_le L (i.val + 1)
      rw [hsucc] at hle
      simp only [fromTokens] at hl
      have hvl : v.length = (renderEncoded (L.take i.val)).length := by rw [← vbytes_len, hv]
      apply spec_bind (push_spec v 47#u8 (by simp at hle; scalar_tac))
      intro v1 hv1
      step as ⟨t, ht⟩
      apply spec_bind (extend_spec v1 (alloc.vec.Vec.deref t) (by
        have : v1.length = v.length + 1 := by rw [← vbytes_len, hv1]; simp [vbytes_len]
        have hvt := vbytes_len (ts.val[i.val])
        simp only [alloc.vec.Vec.length] at hvt
        simp only [List.length_append, List.length_cons] at hle
        simp [alloc.vec.Vec.deref]; rw [ht]; simp only [alloc.vec.Vec.length] at this hvl; omega))
      intro v3 hv3
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hv3, hv1, hv, hi2, hsucc, deref_bytes, ht]; simp
    next hge =>
      apply (spec_ok _).mpr
      have : i.val = ts.length := by scalar_tac
      refine ⟨?_, ?_⟩
      · rw [hv, this, show ts.length = L.length by simp [hL], List.take_length]; rfl
      · rw [hv, this, show ts.length = L.length by simp [hL], List.take_length]
        exact validPointer_of_tokOK _ (fun t ht => by
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
          exact tokOK_of_valid _ (hts u hu))
  · exact ⟨by simp, by simp [vbytes, renderEncoded]⟩

/-! ## replace -/

def vlist (v : alloc.vec.Vec (alloc.vec.Vec U8)) : List (List Nat) := v.val.map vbytes

theorem replaceCollect_spec (X : List Nat) (ta : jsonptr.adapted_api.TokensAdapted) (hinv : TokInv ta)
    (v : alloc.vec.Vec (alloc.vec.Vec U8)) (hX : X.length ≤ Usize.max)
    (hsum : vlist v ++ piecesOf ta = encodedTokens X) :
    jsonptr.adapted_api.replace_adapted_loop0 v ta ⦃ w => vlist w = encodedTokens X ⦄ := by
  have hn := encodedTokens_length_le X
  unfold jsonptr.adapted_api.replace_adapted_loop0
  apply loop.spec_decr_nat
    (fun p : alloc.vec.Vec (alloc.vec.Vec U8) × jsonptr.adapted_api.TokensAdapted => (piecesOf p.2).length)
    (fun p => TokInv p.2 ∧ vlist p.1 ++ piecesOf p.2 = encodedTokens X)
  · rintro ⟨w, t⟩ ⟨hi, hs⟩
    simp only at hi hs
    simp only [jsonptr.adapted_api.replace_adapted_loop0.body]
    step with tokensNext_spec t hi as ⟨o, t1, ho, hp1, hi1, _⟩
    cases o with
    | none =>
      apply (spec_ok _).mpr
      cases h : piecesOf t with
      | nil => rw [h] at hs; simpa using hs
      | cons _ _ => rw [h] at ho; simp at ho
    | some tok =>
      cases h : piecesOf t with
      | nil => rw [h] at ho; simp at ho
      | cons p ps =>
        rw [h] at ho hp1 hs; simp at ho
        apply spec_bind (copy_spec tok); intro c hc
        have hwl : w.length < Usize.max := by
          have := congrArg List.length hs
          simp only [vlist, List.length_append, List.length_map, List.length_cons] at this
          simp only [alloc.vec.Vec.length]; omega
        apply spec_bind (alloc.vec.Vec.push_spec w c hwl); intro w2 hw2
        apply (spec_ok _).mpr
        dsimp only
        refine ⟨hi1, ?_, by rw [hp1]; simp⟩
        rw [hp1, vlist, hw2]; simp [hc, ho]; rw [← hs]; simp [vlist]
  · exact ⟨hinv, hsum⟩

theorem replaceRender_spec (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (hb : (renderEncoded (vlist v)).length < Usize.max) :
    jsonptr.adapted_api.replace_adapted_loop1 v (alloc.vec.Vec.new U8) 0#usize ⦃ w =>
      vbytes w = renderEncoded (vlist v) ⦄ := by
  set L := vlist v with hL
  unfold jsonptr.adapted_api.replace_adapted_loop1
  apply loop.spec_decr_nat (fun p : alloc.vec.Vec U8 × Usize => v.length - p.2.val)
    (fun p => p.2.val ≤ v.length ∧ vbytes p.1 = renderEncoded (L.take p.2.val))
  · rintro ⟨w, i⟩ ⟨hi, hw⟩
    simp only at hi hw
    simp only [jsonptr.adapted_api.replace_adapted_loop1.body]
    split
    next hlt =>
      have hil : i.val < v.length := by scalar_tac
      have hti : L[i.val]? = some (vbytes v.val[i.val]) := by
        simp [hL, vlist, List.getElem?_map, List.getElem?_eq_getElem hil]
      have hsucc := renderEncoded_take_succ L i.val _ hti
      have hle := renderEncoded_length_take_le L (i.val + 1)
      rw [hsucc] at hle
      simp only [List.length_append, List.length_cons] at hle
      have hvl : w.length = (renderEncoded (L.take i.val)).length := by rw [← vbytes_len, hw]
      have hvt := vbytes_len (v.val[i.val])
      simp only [alloc.vec.Vec.length] at hvt hvl
      apply spec_bind (push_spec w 47#u8 (by simp only [alloc.vec.Vec.length]; omega))
      intro w1 hw1
      step as ⟨t, ht⟩
      apply spec_bind (extend_spec w1 (alloc.vec.Vec.deref t) (by
        have : w1.length = w.length + 1 := by rw [← vbytes_len, hw1]; simp [vbytes_len]
        simp only [alloc.vec.Vec.length] at this
        simp [alloc.vec.Vec.deref]; rw [ht]; omega))
      intro w3 hw3
      step as ⟨i2, hi2⟩
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hw3, hw1, hw, hi2, hsucc, deref_bytes, ht]; simp
    next hge =>
      apply (spec_ok _).mpr
      show vbytes w = renderEncoded L
      have : i.val = v.length := by scalar_tac
      rw [hw, this, show v.length = L.length by simp [hL, vlist], List.take_length]
  · exact ⟨by simp, by simp [vbytes, renderEncoded]⟩

theorem replaceAdapted : ReplaceContract := by
  intro buf index t hv ht hb
  have hd : bytes (alloc.vec.Vec.deref buf) = vbytes buf := deref_bytes buf
  apply (fun h => by obtain ⟨⟨r, v⟩, h1, h2⟩ := ok_of_spec h; exact ⟨r, v, h1, h2⟩ :
    jsonptr.adapted_api.replace_adapted buf index t ⦃ p => ValidPointer (vbytes p.2) ∧
      match p.1 with
      | .Ok none => False
      | .Ok (some old) => replaceToken (vbytes buf) index.val (bytes t) = .ok (vbytes p.2, vbytes old) ∧
          ValidEncodedToken (vbytes old)
      | .Err e => replaceToken (vbytes buf) index.val (bytes t) = .error ⟨e.index.val, e.count.val⟩ ∧
          vbytes p.2 = vbytes buf ⦄ → _)
  simp only [jsonptr.adapted_api.replace_adapted]
  split
  next h0 =>
    have hnil : vbytes buf = [] := by
      have : buf.length = 0 := by scalar_tac
      simpa [vbytes] using this
    have hv' : ValidPtr (alloc.vec.Vec.deref buf) := by rw [ValidPtr, hd]; exact hv
    obtain ⟨n, hn, hnv⟩ := countAdapted _ hv'
    rw [hn]
    apply spec_bind_ok
    apply (spec_ok _).mpr
    rw [hd, hnil] at hnv
    refine ⟨hv, ?_, rfl⟩
    simp [replaceToken, hnil, encodedTokens_nil, hnv, count]
  next h0 =>
    set ts := encodedTokens (vbytes buf) with hts
    have hXl : (vbytes buf).length ≤ Usize.max := by rw [vbytes_len]; scalar_tac
    apply spec_bind (tokens_spec (alloc.vec.Vec.deref buf))
    rintro ta ⟨hp, hinv, _⟩
    rw [hd] at hp
    apply spec_bind (replaceCollect_spec (vbytes buf) ta hinv (alloc.vec.Vec.new _) hXl
      (by simp [vlist, hp]))
    intro v hvv
    have hvlen : v.length = ts.length := by
      have := congrArg List.length hvv; simp [vlist] at this; exact this
    split
    next hge =>
      apply (spec_ok _).mpr
      have hnone : ts[index.val]? = none := List.getElem?_eq_none (by scalar_tac)
      refine ⟨hv, ?_, rfl⟩
      simp only [replaceToken, ← hts, hnone]
      congr 2; scalar_tac
    next hlt =>
      have hil : index.val < v.length := by scalar_tac
      rw [if_pos (by scalar_tac)]
      step as ⟨c, hc⟩
      apply spec_bind (copy_spec (alloc.vec.Vec.deref c)); intro old hold
      apply spec_bind (copy_spec t); intro tv htv
      step as ⟨cc, back, hcc, hback⟩
      have hilt : index.val < ts.length := by omega
      have hold' : vbytes old = ts[index.val]'hilt := by
        rw [hold, deref_bytes, hc]
        have := congrArg (fun l => l[index.val]?) hvv
        simp [vlist, List.getElem?_map, List.getElem?_eq_getElem hil] at this
        rw [List.getElem?_eq_getElem hilt] at this; simpa using this
      have hset : vlist (back tv) = ts.set index.val (bytes t) := by
        rw [hback]; simp [vlist, htv]; rw [show List.map vbytes v.val = ts from hvv]
      have hfin : (renderEncoded (vlist (back tv))).length < Usize.max := by
        rw [hset]
        apply isize_le_usize
        apply hb _ (vbytes old)
        simp [replaceToken, ← hts, List.getElem?_eq_getElem (show index.val < ts.length by omega), hold']
      apply spec_bind (replaceRender_spec (back tv) hfin)
      intro w hw
      apply (spec_ok _).mpr
      rw [hset] at hw
      refine ⟨?_, ?_⟩
      · rw [hw]
        apply validPointer_of_tokOK
        intro u hu
        rcases List.mem_or_eq_of_mem_set hu with h | h
        · exact tokOK_of_validPointer _ hv u h
        · rw [h]; exact tokOK_of_valid _ ht
      · refine ⟨by simp [replaceToken, ← hts, List.getElem?_eq_getElem (show index.val < ts.length by omega), hold', hw], ?_⟩
        rw [hold']; exact validEncodedToken_of_valid_mem _ _ hv (List.getElem_mem _)

end JsonptrExtProofs
