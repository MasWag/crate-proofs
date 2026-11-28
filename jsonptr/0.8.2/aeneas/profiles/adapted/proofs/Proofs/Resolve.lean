import Proofs.Codec
import Proofs.Index
import Proofs.Split

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

/-! ## Target 7: JSON `Resolve::resolve` over the local document type -/

/-! ### The abstraction to the specification tree -/

theorem toTrees_eq {n : Nat} (l : Aeneas.Data.ListN.ListN jsonptr.resolve.DocAdapted n) :
    toTrees l = l.toList.map toTree := by
  induction l with
  | nil => simp [toTrees, Aeneas.Data.ListN.ListN.toList]
  | cons c cs ih => simp [toTrees, Aeneas.Data.ListN.ListN.toList, ih]

theorem toMembers_eq {n : Nat}
    (l : Aeneas.Data.ListN.ListN (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) n) :
    toMembers l = l.toList.map (fun p => (vbytes p.1, toTree p.2)) := by
  induction l with
  | nil => simp [toMembers, Aeneas.Data.ListN.ListN.toList]
  | cons c cs ih => obtain ⟨k, d⟩ := c; simp [toMembers, Aeneas.Data.ListN.ListN.toList, ih]

theorem toTree_array (v : alloc.vec.Vec jsonptr.resolve.DocAdapted) :
    toTree (.Array v) = .arr (v.val.map toTree) := by
  obtain ⟨⟨n, l, h⟩⟩ := v
  simp [toTree, toTrees_eq, alloc.vec.Vec.val, Slice.val]

def memberView (p : alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) : List Nat × Tree :=
  (vbytes p.1, toTree p.2)

theorem toTree_object (v : alloc.vec.Vec (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) :
    toTree (.Object v) = .obj (v.val.map memberView) := by
  obtain ⟨⟨n, l, h⟩⟩ := v
  simp [toTree, toMembers_eq, alloc.vec.Vec.val, Slice.val, memberView]

/-! ### Byte equality and first-match lookup (local stand-ins, not release code) -/

theorem bytes_inj (a b : Slice U8) : bytes a = bytes b ↔ a.val = b.val := by
  constructor
  · intro h
    apply List.map_injective_iff.mpr (fun x y hxy => UScalar.eq_of_val_eq hxy)
    exact h
  · intro h; simp [bytes, h]

theorem bytesEq_spec (a b : Slice U8) :
    jsonptr.resolve.bytes_eq_adapted a b ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold jsonptr.resolve.bytes_eq_adapted
  dsimp only
  split
  next hne =>
    apply (spec_ok _).mpr
    have : a.val.length ≠ b.val.length := by
      intro h; apply (bne_iff_ne).mp hne; apply UScalar.eq_of_val_eq; simpa using h
    simp only [Bool.false_eq_true, false_iff]
    intro h; exact this (by rw [h])
  next heq =>
    have hlen : a.val.length = b.val.length := by
      simpa using heq
    unfold jsonptr.resolve.bytes_eq_adapted_loop
    apply loop.spec_decr_nat (fun i : Usize => a.length - i.val)
      (fun i => i.val ≤ a.length ∧ ∀ (k : Nat), k < i.val → a.val[k]? = b.val[k]?)
    · rintro i ⟨hle, hall⟩
      simp only [jsonptr.resolve.bytes_eq_adapted_loop.body]
      split
      next hlt =>
        have hia : i.val < a.length := by scalar_tac
        have hib : i.val < b.length := by scalar_tac
        apply spec_bind (Slice.index_usize_spec a i hia)
        intro x hx
        apply spec_bind (Slice.index_usize_spec b i hib)
        intro y hy
        split
        next hxy =>
          apply (spec_ok _).mpr
          simp only [Bool.false_eq_true, false_iff]
          intro h
          apply bne_val hxy
          rw [hx, hy]; congr 1; simp [h]
        next hxy =>
          have exy : x = y := UScalar.eq_of_val_eq (by simpa using hxy)
          step as ⟨i', hi'⟩
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          intro k hk
          by_cases hki : k < i.val
          · exact hall k hki
          · have : k = i.val := by scalar_tac
            subst this
            rw [List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib, ← hx, ← hy, exy]
      next hge =>
        apply (spec_ok _).mpr
        simp only [true_iff]
        apply List.ext_getElem?
        intro k
        by_cases hk : k < i.val
        · exact hall k hk
        · rw [List.getElem?_eq_none (by scalar_tac), List.getElem?_eq_none (by scalar_tac)]
    · exact ⟨by scalar_tac, fun k hk => by scalar_tac⟩

theorem lookup_spec (members : Slice (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (key : Slice U8) :
    jsonptr.resolve.lookup_adapted members key
      ⦃ o => o.map toTree = lookupKey (bytes key) (members.val.map memberView) ⦄ := by
  unfold jsonptr.resolve.lookup_adapted jsonptr.resolve.lookup_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => members.length - i.val)
    (fun i => i.val ≤ members.length ∧
      lookupKey (bytes key) ((members.val.drop i.val).map memberView) =
        lookupKey (bytes key) (members.val.map memberView))
  · rintro i ⟨hle, hrest⟩
    simp only [jsonptr.resolve.lookup_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < members.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec members i hi)
      rintro ⟨v, da⟩ hx
      have hdrop : members.val.drop i.val = (v, da) :: members.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hi, ← hx]
      rw [hdrop] at hrest
      apply spec_bind (bytesEq_spec (alloc.vec.Vec.deref v) key)
      intro b hb
      have hderef : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
      have hkey : (b = true) ↔ vbytes v = bytes key := by
        rw [hb, ← bytes_inj]; simp only [bytes, vbytes, hderef]
      split
      next htrue =>
        apply (spec_ok _).mpr
        rw [← hrest]
        simp [memberView, hkey.mp htrue, lookupKey]
      next hfalse =>
        step as ⟨i', hi'⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [← hrest, hi']
        have : ¬ vbytes v = bytes key := fun h => hfalse (hkey.mpr h)
        simp [memberView, lookupKey, this]
    next hge =>
      apply (spec_ok _).mpr
      have : i.val = members.val.length := by scalar_tac
      rw [this, List.drop_length] at hrest
      rw [← hrest]; simp [lookupKey]
  · exact ⟨by scalar_tac, by simp⟩

/-! ### One iteration of the release loop -/

/-- The specification's sanity fact `forLen_ok_lt`, proved. -/
theorem forLen_ok_lt (i : Index) (length n : Nat) (h : forLen i length = .ok n) : n < length := by
  cases i with
  | num m =>
    simp only [forLen] at h
    by_cases hc : m < length
    · simp [hc] at h; omega
    · simp [hc] at h
  | next => simp [forLen] at h

theorem forLen_ok (i : jsonptr.index.Index) (len : Usize) :
    ∃ r, i.for_len len = .ok r ∧
      match r with
      | .Ok n => forLen (index i) len.val = .ok n.val
      | .Err e => forLen (index i) len.val = .error ⟨e.length.val, e.index.val⟩ := by
  cases i with
  | Num n =>
    by_cases h : n < len
    · refine ⟨.Ok n, by simp [jsonptr.index.Index.for_len, h], ?_⟩
      have : n.val < len.val := by scalar_tac
      simp [forLen, index, this]
    · refine ⟨.Err ⟨len, n⟩, by simp [jsonptr.index.Index.for_len, h], ?_⟩
      have : ¬ n.val < len.val := by scalar_tac
      simp [forLen, index, this]
  | Next =>
    refine ⟨.Err ⟨len, len⟩, by simp [jsonptr.index.Index.for_len], ?_⟩
    simp [forLen, index]

/-- Support theorem for target 7: one iteration of the release loop. -/
theorem resolveStepAdapted : ResolveStepContract := by
  intro value tok position offset k hk hbound
  cases value with
  | Leaf p =>
    refine ⟨_, by simp [jsonptr.resolve.resolve_step_adapted]; rfl, ?_⟩
    simp [resolveOutcome, resolveError, resolveFrom, toTree]
  | Array v =>
    obtain ⟨r, hr, hpost⟩ := fromStrAdapted tok
    rw [← hk] at hpost
    rw [toTree_array]
    cases r with
    | Err e =>
      refine ⟨.Err (.FailedToParseIndex position offset e), ?_, ?_⟩
      · simp [jsonptr.resolve.resolve_step_adapted, hr]
      · simp only [indexOutcome] at hpost
        simp [resolveOutcome, resolveError, resolveFrom, ← hpost]
    | Ok i =>
      simp only [indexOutcome] at hpost
      obtain ⟨r1, hr1, hpost1⟩ := forLen_ok i (alloc.vec.Vec.len v)
      have hl : (alloc.vec.Vec.len v).val = v.val.length := by simp
      cases r1 with
      | Err e =>
        refine ⟨.Err (.OutOfBounds position offset e), ?_, ?_⟩
        · simp [jsonptr.resolve.resolve_step_adapted, hr, hr1]
        · simp only [hl] at hpost1
          simp [resolveOutcome, resolveError, resolveFrom, ← hpost, hpost1]
      | Ok n =>
        simp only [hl] at hpost1
        have hn : n.val < v.length := forLen_ok_lt _ _ _ hpost1
        refine ⟨.Ok (v.val[n.val]'hn), ?_, ?_⟩
        · simp [jsonptr.resolve.resolve_step_adapted, hr, hr1, alloc.vec.Vec.index_usize,
            List.getElem?_eq_getElem hn]
        · have hg : v.val[n.val]? = some (v.val[n.val]'hn) := List.getElem?_eq_getElem hn
          simp [resolveOutcome, resolveFrom, ← hpost, hpost1, hg]
  | Object v =>
    rw [toTree_object]
    obtain ⟨o, ho, hpost⟩ := decodedAdapted tok hbound
    have hderef : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
    cases o with
    | none =>
      have hkey : k = bytes tok := hpost.2 k hk
      obtain ⟨o1, ho1, hpost1⟩ := ok_of_spec (lookup_spec (alloc.vec.Vec.deref v) tok)
      rw [hderef, ← hkey] at hpost1
      cases o1 with
      | none =>
        refine ⟨.Err (.NotFound position offset), ?_, ?_⟩
        · simp [jsonptr.resolve.resolve_step_adapted, ho, ho1]
        · simp [resolveOutcome, resolveError, resolveFrom, ← hpost1]
      | some da =>
        refine ⟨.Ok da, ?_, ?_⟩
        · simp [jsonptr.resolve.resolve_step_adapted, ho, ho1]
        · simp [resolveOutcome, resolveFrom, ← hpost1]
    | some v1 =>
      have hkey : k = vbytes v1 := hpost.2 k hk
      obtain ⟨o1, ho1, hpost1⟩ := ok_of_spec (lookup_spec (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref v1))
      have hb1 : bytes (alloc.vec.Vec.deref v1) = k := by
        rw [hkey]; simp [bytes, vbytes, alloc.vec.Vec.deref]
      rw [hderef, hb1] at hpost1
      cases o1 with
      | none =>
        refine ⟨.Err (.NotFound position offset), ?_, ?_⟩
        · simp [jsonptr.resolve.resolve_step_adapted, ho, ho1]
        · simp [resolveOutcome, resolveError, resolveFrom, ← hpost1]
      | some da =>
        refine ⟨.Ok da, ?_, ?_⟩
        · simp [jsonptr.resolve.resolve_step_adapted, ho, ho1]
        · simp [resolveOutcome, resolveFrom, ← hpost1]

/-! ### The recursive form of the release loop -/

theorem resolveRec (keys : List (List Nat)) :
    ∀ (value : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (position offset : Usize),
      render keys = bytes ptr → SliceBound ptr →
      position.val + ptr.length ≤ Usize.max → offset.val + ptr.length ≤ Usize.max →
      ∃ r, jsonptr.resolve.resolve_rec_adapted value ptr position offset = .ok r ∧
        resolveOutcome r = resolveFrom Usize.max position.val offset.val (toTree value) keys := by
  induction keys with
  | nil =>
    intro value ptr position offset hr hbound hp ho
    have hnil : bytes ptr = [] := by rw [← hr]; rfl
    obtain ⟨sr, hsr, hspost⟩ := splitFrontAdapted ptr (Or.inl hnil)
    cases sr with
    | none =>
      refine ⟨.Ok value, ?_, ?_⟩
      · rw [jsonptr.resolve.resolve_rec_adapted]; simp [hsr]
      · simp [resolveOutcome, resolveFrom]
    | some p =>
      obtain ⟨tok, rem⟩ := p
      have := hspost.1; rw [hnil] at this; simp at this
  | cons k ks ih =>
    intro value ptr position offset hr hbound hp ho
    have hb : bytes ptr = 47 :: (encode k ++ render ks) := by rw [← hr]; rfl
    obtain ⟨sr, hsr, hspost⟩ := splitFrontAdapted ptr (Or.inr (by rw [hb]; rfl))
    cases sr with
    | none => simp only at hspost; rw [hb] at hspost; simp at hspost
    | some p =>
      obtain ⟨tok, rem⟩ := p
      obtain ⟨hcat, h47, hremh, _⟩ := hspost
      rw [hb] at hcat
      simp only [List.cons.injEq, true_and] at hcat
      obtain ⟨htok, hrem⟩ := Model.split_unique _ _ _ _ (Model.slash_notMem_encode k) h47
        (Model.render_head ks) hremh hcat
      have hlen : ptr.length = 1 + tok.length + rem.length := by
        rw [← bytes_length ptr, hb, htok, hrem, ← bytes_length tok, ← bytes_length rem]
        simp; omega
      have htb : SliceBound tok := by unfold SliceBound at hbound ⊢; omega
      have hrb : SliceBound rem := by unfold SliceBound at hbound ⊢; omega
      obtain ⟨r1, hr1, hpost1⟩ := resolveStepAdapted value tok position offset k htok htb
      rw [Model.resolveFrom_cons, ← hpost1]
      cases r1 with
      | Err e =>
        refine ⟨.Err e, ?_, rfl⟩
        rw [jsonptr.resolve.resolve_rec_adapted]; simp [hsr, hr1]
      | Ok da =>
        rw [jsonptr.resolve.resolve_rec_adapted]
        simp only [hsr, bind_ok]
        simp only [resolveOutcome]
        apply ok_of_spec
        simp only [Std.uncurry]
        rw [hr1, bind_ok]
        simp only [bind_ok]
        step as ⟨i1, hi1⟩
        step as ⟨i2, hi2⟩
        step as ⟨i3, hi3⟩
        have hk : (encode k).length = tok.length := by rw [htok, bytes_length]
        obtain ⟨r2, hr2, hpost2⟩ := ih da rem i3 i2 hrem hrb (by scalar_tac) (by scalar_tac)
        rw [hr2]
        apply (spec_ok _).mpr
        simp only [resolveOutcome] at hpost2
        have e1 : i3.val = position.val + 1 := by scalar_tac
        have e2 : i2.val = offset.val + 1 + (encode k).length := by rw [hk]; scalar_tac
        rw [hpost2, e1, e2]

/-- Target 7, JSON `Resolve::resolve` over the local document type, in the
approved tail-recursive form. -/
theorem resolveAdapted : ResolveContract := by
  intro doc ptr keys hr hbound
  have hb := sliceBound_le hbound
  obtain ⟨r, hres, hpost⟩ := resolveRec keys doc ptr 0#usize 0#usize hr hbound
    (by simp) (by simp)
  exact ⟨r, by simp [jsonptr.resolve.resolve_recursive_adapted, hres], by simpa [resolve] using hpost⟩

end JsonptrAdaptedProofs
