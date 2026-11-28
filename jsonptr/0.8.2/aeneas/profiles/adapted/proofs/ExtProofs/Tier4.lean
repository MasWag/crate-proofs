import Statements.Tier4Mut
import ExtProofs.Tier3
import Proofs

/-! # Tier 4 proofs (sections 15-17), implementation agent -/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrSpecModel.Ext JsonptrAdaptedSpec JsonptrExtSpec

namespace JsonptrExtProofs

abbrev memberView := JsonptrAdaptedProofs.memberView

theorem decodedKey_spec (tok : Slice U8) (k : List Nat) (hk : encode k = bytes tok) (hb : SliceBound tok) :
    jsonptr.adapted_api.doc_mut.decoded_key_adapted tok ⦃ v => vbytes v = k ⦄ := by
  obtain ⟨o, ho, hpost⟩ := JsonptrAdaptedProofs.decodedAdapted tok hb
  unfold jsonptr.adapted_api.doc_mut.decoded_key_adapted
  rw [ho]
  apply spec_bind_ok
  cases o with
  | none =>
    apply spec_mono (copy_spec tok); intro v hv; rw [hv]; exact (hpost.2 k hk).symm
  | some v => exact (spec_ok _).mpr (hpost.2 k hk).symm

/-- First index of a member keyed `k`. -/
def FindPost (ms : List (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (k : List Nat) : Option Usize → Prop
  | none => ∀ p ∈ ms, vbytes p.1 ≠ k
  | some i => ∃ p, ms[i.val]? = some p ∧ vbytes p.1 = k ∧ ∀ j q, j < i.val → ms[j]? = some q → vbytes q.1 ≠ k

theorem findKey_spec (ms : Slice (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (key : Slice U8) :
    jsonptr.adapted_api.doc_mut.find_key_adapted ms key ⦃ FindPost ms.val (bytes key) ⦄ := by
  unfold jsonptr.adapted_api.doc_mut.find_key_adapted jsonptr.adapted_api.doc_mut.find_key_adapted_loop
  apply loop.spec_decr_nat (fun i : Usize => ms.length - i.val)
    (fun i => i.val ≤ ms.length ∧ ∀ j q, j < i.val → ms.val[j]? = some q → vbytes q.1 ≠ bytes key)
  · rintro i ⟨hle, hall⟩
    simp only [jsonptr.adapted_api.doc_mut.find_key_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < ms.length := by scalar_tac
      apply spec_bind (Slice.index_usize_spec ms i hi)
      rintro ⟨v, d⟩ hx
      have hx' : ms.val[i.val]? = some (v, d) := by rw [List.getElem?_eq_getElem hi, ← hx]
      apply spec_bind (JsonptrAdaptedProofs.bytesEq_spec (alloc.vec.Vec.deref v) key)
      intro b hb
      have hkey : (b = true) ↔ vbytes v = bytes key := by
        rw [hb, ← JsonptrAdaptedProofs.bytes_inj]; simp [bytes, vbytes, alloc.vec.Vec.deref]
      split
      next ht =>
        apply (spec_ok _).mpr
        exact ⟨(v, d), hx', hkey.mp ht, hall⟩
      next hf =>
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        intro j q hj hq
        by_cases hji : j < i.val
        · exact hall j q hji hq
        · have : j = i.val := by scalar_tac
          subst this
          rw [hx'] at hq; cases hq
          exact fun h => hf (hkey.mpr h)
    next hge =>
      apply (spec_ok _).mpr
      intro p hp
      obtain ⟨j, hj, hjp⟩ := List.getElem_of_mem hp
      exact hall j p (by scalar_tac) (by rw [List.getElem?_eq_getElem hj, hjp])
  · exact ⟨by scalar_tac, fun j q hj => by simp at hj⟩

theorem keyed_some (k : List Nat) (c : Tree) : ∀ (L : List (List Nat × Tree)) (i : Nat) (p : List Nat × Tree),
    L[i]? = some p → p.1 = k → (∀ j q, j < i → L[j]? = some q → q.1 ≠ k) →
    lookupKey k L = some p.2 ∧ setKey k c L = L.set i (p.1, c) ∧ eraseKey k L = L.eraseIdx i := by
  intro L
  induction L with
  | nil => intro i p h; simp at h
  | cons q L ih =>
    intro i p hp hk hbefore
    cases i with
    | zero =>
      simp at hp; subst hp
      obtain ⟨k', d⟩ := q
      simp only at hk; subst hk
      simp [lookupKey, setKey, eraseKey]
    | succ i =>
      have hq : q.1 ≠ k := hbefore 0 q (by omega) rfl
      obtain ⟨k', d⟩ := q
      have := ih i p (by simpa using hp) hk (fun j q' hj hq' => hbefore (j + 1) q' (by omega) (by simpa using hq'))
      simp only at hq
      simp [lookupKey, setKey, eraseKey, hq, this]

theorem keyed_none (k : List Nat) : ∀ (L : List (List Nat × Tree)), (∀ q ∈ L, q.1 ≠ k) → lookupKey k L = none := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons q L ih =>
    intro h
    obtain ⟨k', d⟩ := q
    have h1 := h (k', d) (by simp)
    simp only at h1
    simp [lookupKey, h1, ih (fun q hq => h q (by simp [hq]))]

theorem findPost_model (ms : List (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (k : List Nat) (c : Tree)
    (i : Usize) (p : alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) (h : FindPost ms k (some i))
    (hp : ms[i.val]? = some p) :
    lookupKey k (ms.map memberView) = some (toTree p.2) ∧
    setKey k c (ms.map memberView) = (ms.map memberView).set i.val (vbytes p.1, c) ∧
    eraseKey k (ms.map memberView) = (ms.map memberView).eraseIdx i.val := by
  obtain ⟨p', hp', hk, hb⟩ := h
  rw [hp] at hp'; cases hp'
  have := keyed_some k c (ms.map memberView) i.val (memberView p) (by simp [hp]) hk
    (fun j q hj hq => by
      simp only [List.getElem?_map] at hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hb j q' hj hq')
  simpa [memberView, JsonptrAdaptedProofs.memberView] using this

theorem findPost_none (ms : List (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (k : List Nat)
    (h : FindPost ms k none) : lookupKey k (ms.map memberView) = none :=
  keyed_none k _ (fun q hq => by
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact h q' hq')

/-! ## `resolve_mut` -/

theorem resolveMutStep (value : jsonptr.resolve.DocAdapted) (tok : Slice U8) (position offset : Usize)
    (k : List Nat) (hk : encode k = bytes tok) (hb : SliceBound tok) :
    ∃ r back, jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted value tok position offset = .ok (r, back) ∧
      resolveOutcome r = resolveFrom Usize.max position.val offset.val (toTree value) [k] ∧
      (∀ e x, r = .Err e → back x = value) ∧
      (∀ n, r = .Ok n → back (.Ok n) = value ∧ ∃ f : Tree → Tree,
        (∀ new, toTree (back (.Ok new)) = f (toTree new)) ∧
        (∀ ks t, replaceAt Usize.max (toTree value) (k :: ks) t = (replaceAt Usize.max (toTree n) ks t).map f)) := by
  cases value with
  | Leaf p =>
    refine ⟨.Err (.Unreachable position offset), fun _ => .Leaf p,
      by simp [jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted], ?_, fun _ _ _ => rfl, fun n h => by cases h⟩
    simp [resolveOutcome, resolveError, resolveFrom, toTree]
  | Array v =>
    obtain ⟨r, hr, hpost⟩ := JsonptrAdaptedProofs.fromStrAdapted tok
    rw [← hk] at hpost
    cases r with
    | Err e =>
      refine ⟨.Err (.FailedToParseIndex position offset e), fun _ => .Array v,
        by simp [jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted, hr], ?_, fun _ _ _ => rfl, fun n h => by cases h⟩
      simp only [indexOutcome] at hpost
      simp [resolveOutcome, resolveError, resolveFrom, JsonptrAdaptedProofs.toTree_array, ← hpost]
    | Ok i =>
      simp only [indexOutcome] at hpost
      obtain ⟨r1, hr1, hpost1⟩ := JsonptrAdaptedProofs.forLen_ok i (alloc.vec.Vec.len v)
      have hl : (alloc.vec.Vec.len v).val = v.val.length := by simp
      cases r1 with
      | Err e =>
        refine ⟨.Err (.OutOfBounds position offset e), fun _ => .Array v,
          by simp [jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted, hr, hr1], ?_, fun _ _ _ => rfl,
          fun n h => by cases h⟩
        simp only [hl] at hpost1
        simp [resolveOutcome, resolveError, resolveFrom, JsonptrAdaptedProofs.toTree_array, ← hpost, hpost1]
      | Ok n =>
        simp only [hl] at hpost1
        have hn : n.val < v.length := JsonptrAdaptedProofs.forLen_ok_lt _ _ _ hpost1
        refine ⟨.Ok (v.val[n.val]'hn), fun r2 => .Array (v.set n (match r2 with | .Ok d => d | _ => v.val[n.val]'hn)),
          ?_, ?_, ?_, ?_⟩
        · simp [jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted, hr, hr1,
            alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hn]
          funext r2; cases r2 <;> rfl
        · have hg : v.val[n.val]? = some (v.val[n.val]'hn) := List.getElem?_eq_getElem hn
          simp [resolveOutcome, resolveFrom, JsonptrAdaptedProofs.toTree_array, ← hpost, hpost1, hg]
        · intro e x h; cases h
        · intro d hd
          cases hd
          refine ⟨?_, fun c => .arr ((v.val.map toTree).set n.val c), ?_, ?_⟩
          · simp; apply alloc.vec.Vec.ext; simp
          · intro new; simp [JsonptrAdaptedProofs.toTree_array, List.map_set]
          · intro ks t
            have hg : (v.val.map toTree)[n.val]? = some (toTree (v.val[n.val]'hn)) := by simp [hn]
            simp [replaceAt, JsonptrAdaptedProofs.toTree_array, ← hpost, hpost1, hg]
  | Object v =>
    have hvd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
    obtain ⟨kv, hkv, hkvb⟩ := ok_of_spec (decodedKey_spec tok k hk hb)
    have hkb : bytes (alloc.vec.Vec.deref kv) = k := by rw [← hkvb]; simp [bytes, vbytes, alloc.vec.Vec.deref]
    obtain ⟨o, ho, hfp⟩ := ok_of_spec (findKey_spec (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref kv))
    rw [hvd, hkb] at hfp
    cases o with
    | none =>
      refine ⟨.Err (.NotFound position offset), fun _ => .Object v,
        by simp [jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted, hkv, ho], ?_, fun _ _ _ => rfl, fun n h => by cases h⟩
      simp [resolveOutcome, resolveError, resolveFrom, JsonptrAdaptedProofs.toTree_object, findPost_none _ _ hfp]
    | some i =>
      obtain ⟨p, hp, hpk, _⟩ := hfp
      have hil : i.val < v.length := (List.getElem?_eq_some_iff.mp hp).1
      have hpe : v.val[i.val]'hil = p := by rw [List.getElem?_eq_getElem hil] at hp; cases hp; rfl
      have hfp' : FindPost v.val k (some i) := ⟨p, hp, hpk, by assumption⟩
      have hlk := (findPost_model v.val k (.leaf 0) i p hfp' hp).1
      refine ⟨.Ok p.2, fun r2 => .Object (v.set i (p.1, match r2 with | .Ok d => d | _ => p.2)), ?_, ?_, ?_, ?_⟩
      · simp [jsonptr.adapted_api.doc_mut.resolve_mut_step_adapted, hkv, ho,
          alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem hil, hpe]
        obtain ⟨p1, p2⟩ := p
        simp only []
        apply congrArg Result.ok; apply Prod.ext; · rfl
        funext r2; cases r2 <;> rfl
      · simp [resolveOutcome, resolveFrom, JsonptrAdaptedProofs.toTree_object, hlk]
      · intro e x h; cases h
      · intro d hd
        cases hd
        refine ⟨?_, fun c => .obj ((v.val.map memberView).set i.val (k, c)), ?_, ?_⟩
        · simp; apply alloc.vec.Vec.ext; simp [← hpe]
        · intro new
          simp [JsonptrAdaptedProofs.toTree_object, List.map_set, memberView, JsonptrAdaptedProofs.memberView, hpk]
        · intro ks t
          have hm := findPost_model v.val k
          simp only [replaceAt, JsonptrAdaptedProofs.toTree_object, hlk]
          cases replaceAt Usize.max (toTree p.2) ks t with
          | none => rfl
          | some c =>
            simp only [Option.map_some]
            rw [(hm c i p hfp' hp).2.1, hpk]

theorem resolveMutRec (keys : List (List Nat)) :
    ∀ (value : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (position offset : Usize),
      render keys = bytes ptr → SliceBound ptr →
      position.val + ptr.length ≤ Usize.max → offset.val + ptr.length ≤ Usize.max →
      ∃ r back, jsonptr.adapted_api.doc_mut.resolve_mut_rec_adapted value ptr position offset = .ok (r, back) ∧
        resolveOutcome r = resolveFrom Usize.max position.val offset.val (toTree value) keys ∧
        (∀ n, r = .Ok n → back (.Ok n) = value ∧
          ∀ new, replaceAt Usize.max (toTree value) keys (toTree new) = some (toTree (back (.Ok new)))) ∧
        (∀ e x, r = .Err e → back x = value) := by
  induction keys with
  | nil =>
    intro value ptr position offset hr hbound hp ho
    have hnil : bytes ptr = [] := by rw [← hr]; rfl
    obtain ⟨sr, hsr, hspost⟩ := JsonptrAdaptedProofs.splitFrontAdapted ptr (Or.inl hnil)
    cases sr with
    | none =>
      refine ⟨.Ok value, fun r => match r with | .Ok d => d | _ => value, ?_, ?_, ?_, ?_⟩
      · rw [jsonptr.adapted_api.doc_mut.resolve_mut_rec_adapted]; simp [hsr]
        funext r; cases r <;> rfl
      · simp [resolveOutcome, resolveFrom]
      · intro n h; cases h; exact ⟨rfl, fun new => by simp [replaceAt]⟩
      · intro e x h; cases h
    | some p =>
      obtain ⟨tok, rem⟩ := p
      have := hspost.1; rw [hnil] at this; simp at this
  | cons k ks ih =>
    intro value ptr position offset hr hbound hp ho
    have hb : bytes ptr = 47 :: (encode k ++ render ks) := by rw [← hr]; rfl
    obtain ⟨sr, hsr, hspost⟩ := JsonptrAdaptedProofs.splitFrontAdapted ptr (Or.inr (by rw [hb]; rfl))
    cases sr with
    | none => simp only at hspost; rw [hb] at hspost; simp at hspost
    | some p =>
      obtain ⟨tok, rem⟩ := p
      obtain ⟨hcat, h47, hremh, _⟩ := hspost
      rw [hb] at hcat
      simp only [List.cons.injEq, true_and] at hcat
      obtain ⟨htok, hrem⟩ := JsonptrAdaptedProofs.Model.split_unique _ _ _ _
        (JsonptrAdaptedProofs.Model.slash_notMem_encode k) h47
        (JsonptrAdaptedProofs.Model.render_head ks) hremh hcat
      have hlen : ptr.length = 1 + tok.length + rem.length := by
        rw [← bytes_length ptr, hb, htok, hrem, ← bytes_length tok, ← bytes_length rem]
        simp; omega
      have htb : SliceBound tok := by unfold SliceBound at hbound ⊢; omega
      have hrb : SliceBound rem := by unfold SliceBound at hbound ⊢; omega
      obtain ⟨r1, sb, hr1, hpost1, herr1, hok1⟩ := resolveMutStep value tok position offset k htok htb
      rw [JsonptrAdaptedProofs.Model.resolveFrom_cons, ← hpost1]
      cases r1 with
      | Err e =>
        refine ⟨.Err e, fun _ => sb (.Err e), ?_, ?_⟩
        · rw [jsonptr.adapted_api.doc_mut.resolve_mut_rec_adapted]; simp [hsr, hr1]
        · refine ⟨by simp [resolveOutcome], ?_, ?_⟩
          · intro n h; cases h
          · intro e' x _; exact herr1 e _ rfl
      | Ok da =>
        obtain ⟨hsame, f, hf, hrep⟩ := hok1 da rfl
        have hk : (encode k).length = tok.length := by rw [htok, bytes_length]
        obtain ⟨i1, hi1, hv1⟩ := ok_of_spec (Usize.add_spec (x := 1#usize) (y := tok.len) (by scalar_tac))
        obtain ⟨i2, hi2, hv2⟩ := ok_of_spec (Usize.add_spec (x := offset) (y := i1) (by scalar_tac))
        obtain ⟨i3, hi3, hv3⟩ := ok_of_spec (Usize.add_spec (x := position) (y := 1#usize) (by scalar_tac))
        obtain ⟨r2, rb, hrec, hpost2, hok2, herr2⟩ := ih da rem i3 i2 hrem hrb (by scalar_tac) (by scalar_tac)
        refine ⟨r2, fun x => sb (.Ok (rb x)), ?_, ?_⟩
        · rw [jsonptr.adapted_api.doc_mut.resolve_mut_rec_adapted]
          simp [hsr, hr1, hi1, hi2, hi3, hrec]
        · have e1 : i3.val = position.val + 1 := by scalar_tac
          have e2 : i2.val = offset.val + 1 + (encode k).length := by rw [hk]; scalar_tac
          refine ⟨?_, ?_, ?_⟩
          · simp only [resolveOutcome] at hpost2 ⊢
            rw [hpost2, e1, e2]
          · intro n hn
            obtain ⟨hs2, hrep2⟩ := hok2 n hn
            refine ⟨by simp only [hs2]; exact hsame, fun new => ?_⟩
            rw [hrep, hrep2 new, Option.map_some, hf]
          · intro e x he
            simp only [herr2 e x he]; exact hsame
  
theorem resolveMutAdapted : ResolveMutContract := by
  intro doc ptr keys hr hbound
  have hb := JsonptrAdaptedProofs.sliceBound_le hbound
  obtain ⟨r, back, hres, hpost⟩ := resolveMutRec keys doc ptr 0#usize 0#usize hr hbound (by simp) (by simp)
  exact ⟨r, back, by simp [jsonptr.adapted_api.doc_mut.resolve_mut_adapted, hres], by simpa [resolve] using hpost.1,
    hpost.2.1, hpost.2.2⟩

/-! ## `expand` -/

theorem render_eq (ks : List (List Nat)) : render ks = renderEncoded (ks.map encode) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [render, renderEncoded, ih]

theorem render_valid (ks : List (List Nat)) : ValidPointer (render ks) := by
  rw [render_eq]
  apply validPointer_of_tokOK
  intro t ht
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp ht
  exact tokOK_of_valid _ ⟨k, rfl⟩

theorem tokens_render (ks : List (List Nat)) : encodedTokens (render ks) = ks.map encode := by
  rw [render_eq]
  apply encodedTokens_renderEncoded
  intro t ht
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp ht
  exact JsonptrAdaptedProofs.Model.slash_notMem_encode k

theorem splitBack_render_snoc (ks : List (List Nat)) (k : List Nat) :
    splitBack (render (ks ++ [k])) = some (render ks, encode k) := by
  have := tokens_render (ks ++ [k])
  simp only [splitBack, this, List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, List.dropLast_concat]
  rw [render_eq]

theorem splitBack_render_nil : splitBack (render []) = none := rfl

def wrap (k : List Nat) (v : Tree) : Tree :=
  if k = [48] ∨ k = [45] then .arr [v] else .obj [(k, v)]

theorem expand_snoc (ks : List (List Nat)) (k : List Nat) (v : Tree) :
    expand (ks ++ [k]) v = expand ks (wrap k v) := by
  induction ks with
  | nil => simp [expand, wrap]
  | cons k' ks ih => simp [expand, ih]

theorem encode_eq_single (k : List Nat) (c : Nat) (hc : c ≠ 47 ∧ c ≠ 126) : encode k = [c] ↔ k = [c] := by
  constructor
  · intro h
    cases k with
    | nil => simp [encode] at h
    | cons b r =>
      by_cases h47 : b = 47
      · subst h47; simp [encode, encodeByte] at h
      · by_cases h126 : b = 126
        · subst h126; simp [encode, encodeByte] at h
        · simp [encode, encodeByte, h47, h126] at h
          obtain ⟨rfl, hr⟩ := h
          cases r with
          | nil => rfl
          | cons b' r' =>
            exfalso
            have := congrArg List.length hr
            have hl : 1 ≤ (encodeByte b').length := by unfold encodeByte; split_ifs <;> simp
            simp only [encode, List.length_append, List.length_cons, List.length_nil] at this
            have : 1 + ((encodeByte b').length + (encode r').length) = 1 := by
              have hb : (encodeByte b).length = 1 := by simp [encodeByte, h47, h126]
              simpa [encode, hb] using this
            omega
  · intro h; subst h; simp [encode, encodeByte, hc.1, hc.2]

theorem vec_single_val {α : Type} (x : α) :
    ∃ w, alloc.vec.Vec.push (alloc.vec.Vec.new α) x = .ok w ∧ w.val = [x] := by
  obtain ⟨w, hw, hv⟩ := ok_of_spec (alloc.vec.Vec.push_spec (alloc.vec.Vec.new α) x (by simp; scalar_tac))
  exact ⟨w, hw, by simpa using hv⟩

theorem toTree_arr_single (w : alloc.vec.Vec jsonptr.resolve.DocAdapted) (d : jsonptr.resolve.DocAdapted)
    (h : w.val = [d]) : toTree (.Array w) = .arr [toTree d] := by
  rw [JsonptrAdaptedProofs.toTree_array, h]; rfl

theorem toTree_obj_single (w : alloc.vec.Vec (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted))
    (kv : alloc.vec.Vec U8) (d : jsonptr.resolve.DocAdapted) (h : w.val = [(kv, d)]) :
    toTree (.Object w) = .obj [(vbytes kv, toTree d)] := by
  rw [JsonptrAdaptedProofs.toTree_object, h]; rfl

theorem bytes_single (s : Slice U8) (c : U8) : bytes s = [c.val] ↔ s.val = [c] := by
  constructor
  · intro h
    cases hs : s.val with
    | nil => simp [bytes, hs] at h
    | cons x r =>
      simp [bytes, hs] at h
      obtain ⟨h1, h2⟩ := h
      subst h2; rw [UScalar.eq_of_val_eq h1]
  · intro h; simp [bytes, h]

theorem wrap_spec (s1 : Slice U8) (k : List Nat) (hk : encode k = bytes s1) (hb : SliceBound s1)
    (value : jsonptr.resolve.DocAdapted) :
    (if s1.len = 1#usize then
        (do
        let i1 ← Slice.index_usize s1 0#usize
        if i1 = 48#u8 then
          let v ← alloc.vec.Vec.push (alloc.vec.Vec.new jsonptr.resolve.DocAdapted) value
          Result.ok (jsonptr.resolve.DocAdapted.Array v)
        else
          if s1.len = 1#usize then
            if i1 = 45#u8 then
              let v ← alloc.vec.Vec.push (alloc.vec.Vec.new jsonptr.resolve.DocAdapted) value
              Result.ok (jsonptr.resolve.DocAdapted.Array v)
            else
              let v ← jsonptr.adapted_api.doc_mut.decoded_key_adapted s1
              let v1 ← alloc.vec.Vec.push (alloc.vec.Vec.new (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (v, value)
              Result.ok (jsonptr.resolve.DocAdapted.Object v1)
          else
            let v ← jsonptr.adapted_api.doc_mut.decoded_key_adapted s1
            let v1 ← alloc.vec.Vec.push (alloc.vec.Vec.new (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (v, value)
            Result.ok (jsonptr.resolve.DocAdapted.Object v1) : Result _)
      else
        if s1.len = 1#usize then
          (do
          let i2 ← Slice.index_usize s1 0#usize
          if i2 = 45#u8 then
            let v ← alloc.vec.Vec.push (alloc.vec.Vec.new jsonptr.resolve.DocAdapted) value
            Result.ok (jsonptr.resolve.DocAdapted.Array v)
          else
            let v ← jsonptr.adapted_api.doc_mut.decoded_key_adapted s1
            let v1 ← alloc.vec.Vec.push (alloc.vec.Vec.new (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (v, value)
            Result.ok (jsonptr.resolve.DocAdapted.Object v1))
        else
          (do
          let v ← jsonptr.adapted_api.doc_mut.decoded_key_adapted s1
          let v1 ← alloc.vec.Vec.push (alloc.vec.Vec.new (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (v, value)
          Result.ok (jsonptr.resolve.DocAdapted.Object v1))) ⦃ d => toTree d = wrap k (toTree value) ⦄ := by
  obtain ⟨kv, hkv, hkb⟩ := ok_of_spec (decodedKey_spec s1 k hk hb)
  obtain ⟨wa, hwa, hwav⟩ := vec_single_val value
  obtain ⟨wo, hwo, hwov⟩ := vec_single_val (kv, value)
  have h48 : k = [48] ↔ s1.val = [48#u8] := by
    rw [← encode_eq_single k 48 (by omega), hk, ← bytes_single s1 48#u8]; simp
  have h45 : k = [45] ↔ s1.val = [45#u8] := by
    rw [← encode_eq_single k 45 (by omega), hk, ← bytes_single s1 45#u8]; simp
  have hobj : toTree (.Object wo) = .obj [(k, toTree value)] := by rw [toTree_obj_single wo kv value hwov, hkb]
  have harr : toTree (.Array wa) = .arr [toTree value] := toTree_arr_single wa value hwav
  cases hs : s1.val with
  | nil =>
    have hl : s1.len ≠ 1#usize := by intro h; have := congrArg UScalar.val h; simp [hs] at this
    have hn48 : ¬ k = [48] := by rw [h48, hs]; simp
    have hn45 : ¬ k = [45] := by rw [h45, hs]; simp
    simp only [hl, ↓reduceIte]; rw [hkv]; apply spec_bind_ok; rw [hwo]; apply spec_bind_ok; apply (spec_ok _).mpr
    simp [hobj, wrap, hn48, hn45]
  | cons x r =>
    cases r with
    | cons y r' =>
      have hl : s1.len ≠ 1#usize := by intro h; have := congrArg UScalar.val h; simp [hs] at this
      have hn48 : ¬ k = [48] := by rw [h48, hs]; simp
      have hn45 : ¬ k = [45] := by rw [h45, hs]; simp
      simp only [hl, ↓reduceIte]; rw [hkv]; apply spec_bind_ok; rw [hwo]; apply spec_bind_ok; apply (spec_ok _).mpr
      simp [hobj, wrap, hn48, hn45]
    | nil =>
      have hl : s1.len = 1#usize := by apply UScalar.eq_of_val_eq; simp [hs]
      have hidx : Slice.index_usize s1 0#usize = .ok x := by simp [Slice.index_usize, hs]
      simp only [hl, ↓reduceIte]; rw [hidx]; apply spec_bind_ok
      by_cases hx48 : x = 48#u8
      · subst hx48
        simp only [↓reduceIte]; rw [hwa]; apply spec_bind_ok; apply (spec_ok _).mpr
        simp [harr, wrap, h48.mpr hs]
      · by_cases hx45 : x = 45#u8
        · subst hx45
          have hn48 : ¬ k = [48] := by rw [h48, hs]; simp
          simp only [hx48, ↓reduceIte]; rw [hwa]; apply spec_bind_ok; apply (spec_ok _).mpr
          simp [harr, wrap, h45.mpr hs]
        · have hn48 : ¬ k = [48] := by rw [h48, hs]; simpa using hx48
          have hn45 : ¬ k = [45] := by rw [h45, hs]; simpa using hx45
          simp only [hx48, hx45, ↓reduceIte]; rw [hkv]; apply spec_bind_ok; rw [hwo]; apply spec_bind_ok; apply (spec_ok _).mpr
          simp [hobj, wrap, hn48, hn45]

theorem render_length_snoc (ks : List (List Nat)) (k : List Nat) :
    (render (ks ++ [k])).length = (render ks).length + 1 + (encode k).length := by
  induction ks with
  | nil => simp [render]; omega
  | cons k' ks ih => simp [render, ih]; omega

theorem expandAdapted : ∀ (n : Nat) (ks : List (List Nat)), ks.length ≤ n →
    ∀ (rem : Slice U8) (v : jsonptr.resolve.DocAdapted), render ks = bytes rem → SliceBound rem →
    ∃ d, jsonptr.adapted_api.doc_mut.expand_adapted rem v = .ok d ∧ toTree d = expand ks (toTree v) := by
  intro n
  induction n with
  | zero =>
    intro ks hks rem v hr hb
    have : ks = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hks)
    subst this
    obtain ⟨sb, hsb, hm, _⟩ := splitBackAdapted rem (by rw [ValidPtr, ← hr]; exact render_valid [])
    rw [← hr] at hm
    cases sb with
    | none => exact ⟨v, by rw [jsonptr.adapted_api.doc_mut.expand_adapted]; simp [hsb], rfl⟩
    | some p => simp [opbytes, splitBack_render_nil] at hm
  | succ n ih =>
    intro ks hks rem v hr hb
    rcases List.eq_nil_or_concat ks with h | ⟨ks', k, hks'⟩
    · subst h; exact ih [] (by simp) rem v hr hb
    · rw [List.concat_eq_append] at hks'; subst hks'
      obtain ⟨sb, hsb, hm, hsplit⟩ := splitBackAdapted rem (by rw [ValidPtr, ← hr]; exact render_valid _)
      rw [← hr, splitBack_render_snoc] at hm
      cases sb with
      | none => simp [opbytes] at hm
      | some p =>
        obtain ⟨s0, s1⟩ := p
        simp [opbytes] at hm
        obtain ⟨h0, h1⟩ := hm
        have hlen := render_length_snoc ks' k
        rw [hr] at hlen
        have hb1 : SliceBound s1 := by
          unfold SliceBound at hb ⊢; rw [← bytes_length s1, h1]; rw [bytes_length] at hlen; omega
        have hb0 : SliceBound s0 := by
          unfold SliceBound at hb ⊢; rw [← bytes_length s0, h0]; rw [bytes_length] at hlen; omega
        rw [jsonptr.adapted_api.doc_mut.expand_adapted]
        simp only [hsb, bind_ok]
        apply ok_of_spec
        apply spec_bind (wrap_spec s1 k h1.symm hb1 v)
        intro da hda
        obtain ⟨d, hd, hdt⟩ := ih ks' (by simp at hks; omega) s0 da h0.symm hb0
        rw [hd]
        apply (spec_ok _).mpr
        rw [hdt, hda, expand_snoc]

/-! ## `assign` -/

theorem treesBound_get (items : List Tree) (h : TreesBound items) (n : Nat) (c : Tree) (hc : items[n]? = some c) :
    TreeBound c := by
  induction items generalizing n with
  | nil => simp at hc
  | cons x xs ih =>
    cases n with
    | zero => simp at hc; subst hc; exact h.1
    | succ n => exact ih h.2 n (by simpa using hc)

theorem membersBound_get (ms : List (List Nat × Tree)) (h : MembersBound ms) (n : Nat) (p : List Nat × Tree)
    (hc : ms[n]? = some p) : TreeBound p.2 := by
  induction ms generalizing n with
  | nil => simp at hc
  | cons x xs ih =>
    obtain ⟨a, c⟩ := x
    cases n with
    | zero => simp at hc; subst hc; exact h.1
    | succ n => exact ih h.2 n (by simpa using hc)

theorem forLenIncl_ok (i : jsonptr.index.Index) (len : Usize) :
    ∃ r, i.for_len_incl len = .ok r ∧
      match r with
      | .Ok n => forLenIncl (index i) len.val = .ok n.val
      | .Err e => forLenIncl (index i) len.val = .error ⟨e.length.val, e.index.val⟩ := by
  cases i with
  | Num n =>
    by_cases h : n ≤ len
    · refine ⟨.Ok n, by simp [jsonptr.index.Index.for_len_incl, h], ?_⟩
      have : n.val ≤ len.val := by scalar_tac
      simp [forLenIncl, index, this]
    · refine ⟨.Err ⟨len, n⟩, by simp [jsonptr.index.Index.for_len_incl, h], ?_⟩
      have : ¬ n.val ≤ len.val := by scalar_tac
      simp [forLenIncl, index, this]
  | Next => exact ⟨.Ok len, by simp [jsonptr.index.Index.for_len_incl], by simp [forLenIncl, index]⟩

theorem forLenIncl_le (i : Index) (len n : Nat) (h : forLenIncl i len = .ok n) : n ≤ len := by
  cases i with
  | num m => simp only [forLenIncl] at h; split at h <;> simp_all
  | next => simp [forLenIncl] at h; omega

/-- The assignment postcondition. -/
def AssignPost (pos off : Nat) (t : Tree) (keys : List (List Nat)) (v : Tree) (doc0 : jsonptr.resolve.DocAdapted) :
    core.result.Result (Option jsonptr.resolve.DocAdapted) jsonptr.adapted_api.doc_mut.AssignErrorAdapted ×
      jsonptr.resolve.DocAdapted → Prop
  | (.Ok old, d') => assignFrom Usize.max pos off t keys v = .ok (toTree d', old.map toTree)
  | (.Err e, d') => assignFrom Usize.max pos off t keys v = .error (assignError e) ∧ d' = doc0

theorem vec_index_mut_eq {α : Type} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.length) :
    alloc.vec.Vec.index_mut_usize v i = .ok (v.val[i.val]'h, v.set i) := by
  simp [alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize, List.getElem?_eq_getElem h]

theorem render_nil_iff (ks : List (List Nat)) : render ks = [] ↔ ks = [] := by
  cases ks <;> simp [render]

theorem assignRec (keys : List (List Nat)) :
    ∀ (value : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (dval : jsonptr.resolve.DocAdapted) (position offset : Usize),
      render keys = bytes ptr → SliceBound ptr →
      position.val + ptr.length ≤ Usize.max → offset.val + ptr.length ≤ Usize.max → TreeBound (toTree value) →
      ∃ res, jsonptr.adapted_api.doc_mut.assign_rec_adapted value ptr dval position offset = .ok res ∧
        AssignPost position.val offset.val (toTree value) keys (toTree dval) value res := by
  induction keys with
  | nil =>
    intro value ptr dval position offset hr hbound hp ho htb
    have hnil : bytes ptr = [] := by rw [← hr]; rfl
    obtain ⟨sr, hsr, hspost⟩ := JsonptrAdaptedProofs.splitFrontAdapted ptr (Or.inl hnil)
    cases sr with
    | none =>
      refine ⟨(.Ok (some value), dval), ?_, ?_⟩
      · rw [jsonptr.adapted_api.doc_mut.assign_rec_adapted]; simp [hsr, core.mem.replace]
      · simp [AssignPost, assignFrom]
    | some p =>
      obtain ⟨tok, rem⟩ := p
      have := hspost.1; rw [hnil] at this; simp at this
  | cons k ks ih =>
    intro value ptr dval position offset hr hbound hp ho htb
    have hb : bytes ptr = 47 :: (encode k ++ render ks) := by rw [← hr]; rfl
    obtain ⟨sr, hsr, hspost⟩ := JsonptrAdaptedProofs.splitFrontAdapted ptr (Or.inr (by rw [hb]; rfl))
    cases sr with
    | none => simp only at hspost; rw [hb] at hspost; simp at hspost
    | some p =>
      obtain ⟨tok, rem⟩ := p
      obtain ⟨hcat, h47, hremh, _⟩ := hspost
      rw [hb] at hcat
      simp only [List.cons.injEq, true_and] at hcat
      obtain ⟨htok, hrem⟩ := JsonptrAdaptedProofs.Model.split_unique _ _ _ _
        (JsonptrAdaptedProofs.Model.slash_notMem_encode k) h47
        (JsonptrAdaptedProofs.Model.render_head ks) hremh hcat
      have hlen : ptr.length = 1 + tok.length + rem.length := by
        rw [← bytes_length ptr, hb, htok, hrem, ← bytes_length tok, ← bytes_length rem]
        simp; omega
      have htb' : SliceBound tok := by unfold SliceBound at hbound ⊢; omega
      have hrb : SliceBound rem := by unfold SliceBound at hbound ⊢; omega
      have hk : (encode k).length = tok.length := by rw [htok, bytes_length]
      have hremE : rem.length = 0 ↔ ks = [] := by
        rw [← render_nil_iff, hrem, ← bytes_length, List.length_eq_zero_iff]
      rw [jsonptr.adapted_api.doc_mut.assign_rec_adapted]
      simp only [hsr, bind_ok]
      apply ok_of_spec
      simp only [Std.uncurry]
      cases value with
      | Leaf lp =>
        obtain ⟨d, hd, hdt⟩ := expandAdapted (k :: ks).length (k :: ks) (le_refl _) ptr dval hr hbound
        simp only []
        rw [hd]; apply spec_bind_ok
        apply (spec_ok _).mpr
        simp [AssignPost, assignFrom, core.mem.replace, hdt, toTree]
      | Array v =>
        rw [JsonptrAdaptedProofs.toTree_array] at htb
        obtain ⟨hvl, hvb⟩ := htb
        simp only []
        obtain ⟨r, hr0, hpost⟩ := JsonptrAdaptedProofs.fromStrAdapted tok
        rw [← htok] at hpost
        rw [hr0]; apply spec_bind_ok
        cases r with
        | Err e =>
          apply (spec_ok _).mpr
          simp only [indexOutcome] at hpost
          simp [AssignPost, assignFrom, JsonptrAdaptedProofs.toTree_array, ← hpost, assignError]
        | Ok i =>
          simp only [indexOutcome] at hpost
          obtain ⟨r1, hr1, hpost1⟩ := forLenIncl_ok i (alloc.vec.Vec.len v)
          have hl : (alloc.vec.Vec.len v).val = v.val.length := by simp
          simp only [hl] at hpost1
          simp only []
          rw [hr1]; apply spec_bind_ok
          cases r1 with
          | Err e =>
            apply (spec_ok _).mpr
            simp [AssignPost, assignFrom, JsonptrAdaptedProofs.toTree_array, ← hpost, hpost1, assignError]
          | Ok n =>
            have hnle : n.val ≤ v.length := forLenIncl_le _ _ _ hpost1
            simp only []
            split
            next hlt =>
              have hn : n.val < v.length := by scalar_tac
              have hg : (v.val.map toTree)[n.val]? = some (toTree (v.val[n.val]'hn)) := by simp [hn]
              step as ⟨bemp, hbemp⟩
              split
              next hempty =>
                have hks : ks = [] := hremE.mp (by simpa [hbemp] using hempty)
                subst hks
                step as ⟨c, back, hc, hback⟩
                show assignFrom Usize.max position.val offset.val (toTree (.Array v)) [k] (toTree dval) =
                  .ok (toTree (.Array (back dval)), (some c).map toTree)
                rw [hback, hc]
                simp only [JsonptrAdaptedProofs.toTree_array, assignFrom, ← hpost, List.length_map, hpost1]
                simp [List.map_set, List.getElem?_eq_getElem hn]
              next hne =>
                have hks : ks ≠ [] := fun h => hne (by simp [hbemp]; exact List.length_eq_zero_iff.mp (hremE.mpr h))
                step as ⟨i5, hi5⟩
                step as ⟨i6, hi6⟩
                step as ⟨i7, hi7⟩
                step as ⟨c, back, hc, hback⟩
                have hcb : TreeBound (toTree c) := by
                  rw [hc]; exact treesBound_get _ hvb n.val _ hg
                obtain ⟨res2, hres2, hpost2⟩ := ih c rem dval i7 i6 hrem hrb (by scalar_tac) (by scalar_tac) hcb
                rw [hres2]; apply spec_bind_ok
                obtain ⟨r2, d2⟩ := res2
                apply (spec_ok _).mpr
                have e1 : i7.val = position.val + 1 := by scalar_tac
                have e2 : i6.val = offset.val + 1 + (encode k).length := by rw [hk]; scalar_tac
                cases r2 with
                | Ok old =>
                  simp only [AssignPost] at hpost2 ⊢
                  rw [e1, e2] at hpost2
                  simp only [JsonptrAdaptedProofs.toTree_array, assignFrom, ← hpost, List.length_map, hpost1]
                  simp [List.getElem?_eq_getElem hn, ← hc, hpost2, hback, List.map_set]
                | Err e =>
                  simp only [AssignPost] at hpost2 ⊢
                  rw [e1, e2] at hpost2
                  obtain ⟨hp2, hd2⟩ := hpost2
                  refine ⟨by simp only [JsonptrAdaptedProofs.toTree_array, assignFrom, ← hpost, List.length_map, hpost1]
                             simp [List.getElem?_eq_getElem hn, ← hc, hp2], ?_⟩
                  rw [hd2, hback, hc]; simp; apply alloc.vec.Vec.ext; simp
            next hge =>
              have hn : n.val = v.length := by scalar_tac
              obtain ⟨d, hd, hdt⟩ := expandAdapted ks.length ks (le_refl _) rem dval hrem hrb
              rw [hd]; apply spec_bind_ok
              obtain ⟨w, hw, hwv⟩ := ok_of_spec (alloc.vec.Vec.push_spec v d (by simpa using hvl))
              rw [hw]; apply spec_bind_ok
              apply (spec_ok _).mpr
              show assignFrom Usize.max position.val offset.val (toTree (.Array v)) (k :: ks) (toTree dval) =
                .ok (toTree (.Array w), (none : Option jsonptr.resolve.DocAdapted).map toTree)
              simp only [JsonptrAdaptedProofs.toTree_array, assignFrom, ← hpost, List.length_map, hpost1]
              simp [hn, hwv, hdt]
      | Object v =>
        rw [JsonptrAdaptedProofs.toTree_object] at htb
        obtain ⟨hvl, hvb⟩ := htb
        have hvd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
        obtain ⟨kv, hkv, hkvb⟩ := ok_of_spec (decodedKey_spec tok k htok htb')
        have hkb : bytes (alloc.vec.Vec.deref kv) = k := by rw [← hkvb]; simp [bytes, vbytes, alloc.vec.Vec.deref]
        obtain ⟨o, ho, hfp⟩ := ok_of_spec (findKey_spec (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref kv))
        rw [hvd, hkb] at hfp
        simp only []
        rw [hkv]; apply spec_bind_ok
        rw [ho]; apply spec_bind_ok
        apply spec_bind (Pₘ := fun t : core.result.Result (Option jsonptr.resolve.DocAdapted)
            jsonptr.adapted_api.doc_mut.AssignErrorAdapted × alloc.vec.Vec (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) × Bool =>
          AssignPost position.val offset.val (toTree (.Object v)) (k :: ks) (toTree dval) (.Object v) (t.1, .Object t.2.1))
        · cases o with
          | none =>
            have hnone := findPost_none _ _ hfp
            obtain ⟨d, hd, hdt⟩ := expandAdapted ks.length ks (le_refl _) rem dval hrem hrb
            rw [hd]; apply spec_bind_ok
            obtain ⟨w, hw, hwv⟩ := ok_of_spec (alloc.vec.Vec.push_spec v (kv, d) (by simpa using hvl))
            rw [hw]; apply spec_bind_ok
            apply (spec_ok _).mpr
            show assignFrom Usize.max position.val offset.val (toTree (.Object v)) (k :: ks) (toTree dval) =
              .ok (toTree (.Object w), (none : Option jsonptr.resolve.DocAdapted).map toTree)
            simp only [JsonptrAdaptedProofs.toTree_object, assignFrom, hnone]
            simp [hwv, JsonptrAdaptedProofs.memberView, hkvb, hdt]
          | some i =>
            obtain ⟨p, hp, hpk, hbef⟩ := hfp
            have hfp' : FindPost v.val k (some i) := ⟨p, hp, hpk, hbef⟩
            have hil : i.val < v.length := (List.getElem?_eq_some_iff.mp hp).1
            have hpe : v.val[i.val]'hil = p := by rw [List.getElem?_eq_getElem hil] at hp; cases hp; rfl
            have hm := findPost_model v.val k
            have hlk := (hm (.leaf 0) i p hfp' hp).1
            step as ⟨bemp, hbemp⟩
            split
            next hempty =>
              have hks : ks = [] := hremE.mp (by simpa [hbemp] using hempty)
              subst hks
              rw [vec_index_mut_eq v i hil, hpe]
              obtain ⟨c1, c2⟩ := p
              simp only [bind_ok, bind_tc_ok, Std.uncurry, core.mem.replace]
              apply (spec_ok _).mpr
              show assignFrom Usize.max position.val offset.val (toTree (.Object v)) [k] (toTree dval) =
                .ok (toTree (.Object (v.set i (c1, dval))), (some c2).map toTree)
              have hcp : (c1, c2) = (c1, c2) := rfl
              simp only [JsonptrAdaptedProofs.toTree_object, assignFrom, hlk]
              rw [(hm (toTree dval) i (c1, c2) hfp' hp).2.1]
              simp only [JsonptrAdaptedProofs.memberView] at hpk
              simp [List.map_set, JsonptrAdaptedProofs.memberView, hpk]
            next hne =>
              have hks : ks ≠ [] := fun h => hne (by simp [hbemp]; exact List.length_eq_zero_iff.mp (hremE.mpr h))
              step as ⟨i5, hi5⟩
              step as ⟨i6, hi6⟩
              step as ⟨i7, hi7⟩
              rw [vec_index_mut_eq v i hil, hpe]
              obtain ⟨c1, c2⟩ := p
              simp only [bind_ok, bind_tc_ok, Std.uncurry]
              have hcp : (c1, c2) = (c1, c2) := rfl
              have hcb : TreeBound (toTree c2) := by
                have := membersBound_get _ hvb i.val (memberView (c1, c2)) (by simp [hp])
                simpa [JsonptrAdaptedProofs.memberView] using this
              obtain ⟨res2, hres2, hpost2⟩ := ih c2 rem dval i7 i6 hrem hrb (by scalar_tac) (by scalar_tac) hcb
              obtain ⟨r2, d2⟩ := res2
              apply spec_bind (Pₘ := fun t => t = (r2, v.set i (c1, d2)))
              · apply spec_bind (show jsonptr.adapted_api.doc_mut.assign_rec_adapted c2 rem dval i7 i6 ⦃ fun x => x = (r2, d2) ⦄ by
                  rw [hres2]; exact (spec_ok _).mpr rfl)
                rintro x rfl
                exact (spec_ok _).mpr rfl
              rintro x rfl
              apply (spec_ok _).mpr
              show AssignPost position.val offset.val (toTree (.Object v)) (k :: ks) (toTree dval) (.Object v)
                (r2, .Object (v.set i (c1, d2)))
              have e1 : i7.val = position.val + 1 := by scalar_tac
              have e2 : i6.val = offset.val + 1 + (encode k).length := by rw [hk]; scalar_tac
              have hlk' : lookupKey k (v.val.map memberView) = some (toTree c2) := by rw [hlk]
              cases r2 with
              | Ok old =>
                simp only [AssignPost] at hpost2 ⊢
                rw [e1, e2] at hpost2
                simp only [JsonptrAdaptedProofs.toTree_object, assignFrom, hlk', hpost2]
                rw [(hm (toTree d2) i (c1, c2) hfp' hp).2.1]
                simp only [JsonptrAdaptedProofs.memberView] at hpk
                simp [List.map_set, JsonptrAdaptedProofs.memberView, hpk]
              | Err e =>
                simp only [AssignPost] at hpost2 ⊢
                rw [e1, e2] at hpost2
                obtain ⟨hp2, hd2⟩ := hpost2
                refine ⟨by simp only [JsonptrAdaptedProofs.toTree_object, assignFrom, hlk', hp2], ?_⟩
                rw [hd2, ← hpe]; simp; apply alloc.vec.Vec.ext; simp
        · rintro ⟨r, v2, b⟩ hpost
          cases b <;> exact (spec_ok _).mpr hpost

theorem assignAdapted : AssignContract := by
  intro doc ptr keys v hr hbound htb
  have hb := JsonptrAdaptedProofs.sliceBound_le hbound
  obtain ⟨res, hres, hpost⟩ := assignRec keys doc ptr v 0#usize 0#usize hr hbound (by simp) (by simp) htb
  obtain ⟨r, d'⟩ := res
  refine ⟨r, d', by simp [jsonptr.adapted_api.doc_mut.assign_adapted, hres], ?_⟩
  cases r with
  | Ok old => simpa [AssignPost, assign] using hpost
  | Err e => simpa [AssignPost, assign] using hpost

/-! ## `delete` -/

theorem eraseIdx_take_succ {α : Type} (l : List α) (i idx : Nat) (hi : i < l.length) (hne : i ≠ idx) :
    (l.take (i + 1)).eraseIdx idx = (l.take i).eraseIdx idx ++ [l[i]] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some]
  by_cases h : idx < i
  · rw [List.eraseIdx_append_of_lt_length (by simp; omega)]
  · rw [List.eraseIdx_append_of_length_le (by simp; omega), List.eraseIdx_of_length_le (by simp; omega)]
    rw [List.eraseIdx_eq_self.mpr (by simp; omega)]

theorem eraseIdx_take_self {α : Type} (l : List α) (i : Nat) (hi : i < l.length) :
    (l.take (i + 1)).eraseIdx i = l.take i := by
  rw [List.eraseIdx_eq_take_drop_succ, List.take_take, List.drop_take]
  simp

theorem removeAt_spec (items : alloc.vec.Vec jsonptr.resolve.DocAdapted) (idx : Usize) (h : idx.val < items.length) :
    jsonptr.adapted_api.doc_mut.remove_at_adapted items idx ⦃ (d : jsonptr.resolve.DocAdapted) w =>
      d = items.val[idx.val] ∧ w.val = items.val.eraseIdx idx.val ⦄ := by
  unfold jsonptr.adapted_api.doc_mut.remove_at_adapted jsonptr.adapted_api.doc_mut.remove_at_adapted_loop
  apply loop.spec_decr_nat
    (fun p : alloc.vec.Vec jsonptr.resolve.DocAdapted × alloc.vec.Vec jsonptr.resolve.DocAdapted ×
      jsonptr.resolve.DocAdapted × Usize => items.length - p.2.2.2.val)
    (fun p => p.2.2.2.val ≤ items.length ∧ p.1.length = items.length ∧ p.1.val.drop p.2.2.2.val = items.val.drop p.2.2.2.val ∧
      p.2.1.val = (items.val.take p.2.2.2.val).eraseIdx idx.val ∧ (idx.val < p.2.2.2.val → p.2.2.1 = items.val[idx.val]))
  · rintro ⟨it, acc, rem, i⟩ ⟨hle, hlen, hdrop, hacc, hrem⟩
    simp only at hle hlen hdrop hacc hrem
    simp only [jsonptr.adapted_api.doc_mut.remove_at_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < items.length := by scalar_tac
      have hit : i.val < it.length := by omega
      have hx : it.val[i.val] = items.val[i.val] := by
        have := congrArg (fun l => l[0]?) hdrop; simp [List.getElem?_drop] at this
        rw [List.getElem?_eq_getElem hit, List.getElem?_eq_getElem hi] at this; simpa using this
      rw [alloc.vec.Vec.index_mut_slice_index, vec_index_mut_eq it i hit]
      simp only [bind_ok, Std.uncurry, core.mem.replace]
      have hdrop' : (it.set i (jsonptr.resolve.DocAdapted.Leaf 0#u64)).val.drop (i.val + 1) = items.val.drop (i.val + 1) := by
        have := congrArg (List.drop 1) hdrop
        simp only [List.drop_drop] at this
        rw [alloc.vec.Vec.set_val_eq, List.drop_set_of_lt (by omega)]
        simpa [Nat.add_comm] using this
      split
      next heq =>
        simp only [bind_ok]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, by simp [hlen], by rw [hi2]; exact hdrop', ?_, ?_, by scalar_tac⟩
        · have hiv : i.val = idx.val := by rw [heq]
          rw [hi2, hacc, ← hiv, eraseIdx_take_self _ _ hi, List.eraseIdx_of_length_le (by simp)]
        · have hiv : i.val = idx.val := by rw [heq]
          intro _; rw [hx]; simp [hiv]
      next hne =>
        have hne' : i.val ≠ idx.val := fun e => hne (by scalar_tac)
        have hal : acc.length < Usize.max := by
          have : acc.length ≤ i.val := by
            have h1 := congrArg List.length hacc
            have h2 := List.length_eraseIdx_le (items.val.take i.val) idx.val
            have h3 : (items.val.take i.val).length ≤ i.val := by simp
            simp only [alloc.vec.Vec.length]; omega
          scalar_tac
        obtain ⟨acc2, hacc2, hav⟩ := ok_of_spec (alloc.vec.Vec.push_spec acc (it.val[i.val]) hal)
        rw [hacc2]; simp only [bind_ok]
        step as ⟨i2, hi2⟩
        refine ⟨by scalar_tac, by simp [hlen], by rw [hi2]; exact hdrop', ?_, ?_, by scalar_tac⟩
        · rw [hi2, hav, hacc, hx, eraseIdx_take_succ _ _ _ hi hne']
        · intro h2; exact hrem (by scalar_tac)
    next hge =>
      apply (spec_ok _).mpr
      have : i.val = items.length := by scalar_tac
      refine ⟨hrem (by omega), ?_⟩
      rw [hacc, this, List.take_length]
  · exact ⟨by simp, rfl, by simp, by simp, fun h => by simp at h⟩

theorem removeMember_spec (ms : alloc.vec.Vec (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted)) (idx : Usize)
    (h : idx.val < ms.length) :
    jsonptr.adapted_api.doc_mut.remove_member_adapted ms idx ⦃ (d : jsonptr.resolve.DocAdapted) w =>
      d = (ms.val[idx.val]).2 ∧ w.val.map memberView = (ms.val.eraseIdx idx.val).map memberView ⦄ := by
  unfold jsonptr.adapted_api.doc_mut.remove_member_adapted jsonptr.adapted_api.doc_mut.remove_member_adapted_loop
  apply loop.spec_decr_nat
    (fun p : alloc.vec.Vec (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) × alloc.vec.Vec (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) ×
      jsonptr.resolve.DocAdapted × Usize => ms.length - p.2.2.2.val)
    (fun p => p.2.2.2.val ≤ ms.length ∧ p.1.length = ms.length ∧ p.1.val.drop p.2.2.2.val = ms.val.drop p.2.2.2.val ∧
      p.2.1.val.map memberView = ((ms.val.take p.2.2.2.val).eraseIdx idx.val).map memberView ∧
      (idx.val < p.2.2.2.val → p.2.2.1 = (ms.val[idx.val]).2))
  · rintro ⟨it, acc, rem, i⟩ ⟨hle, hlen, hdrop, hacc, hrem⟩
    simp only at hle hlen hdrop hacc hrem
    simp only [jsonptr.adapted_api.doc_mut.remove_member_adapted_loop.body]
    split
    next hlt =>
      have hi : i.val < ms.length := by scalar_tac
      have hit : i.val < it.length := by omega
      have hx : it.val[i.val] = ms.val[i.val] := by
        have := congrArg (fun l => l[0]?) hdrop; simp [List.getElem?_drop] at this
        rw [List.getElem?_eq_getElem hit, List.getElem?_eq_getElem hi] at this; simpa using this
      rw [alloc.vec.Vec.index_mut_slice_index, vec_index_mut_eq it i hit]
      rcases hxe : it.val[i.val] with ⟨kk, dd⟩
      simp only [bind_ok, Std.uncurry, core.mem.replace]
      set it2 := it.set i (kk, jsonptr.resolve.DocAdapted.Leaf 0#u64) with hit2
      have hit2l : i.val < it2.length := by simp [hit2]; omega
      have hidx2 : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) it2 i =
          .ok (kk, jsonptr.resolve.DocAdapted.Leaf 0#u64) := by
        rw [alloc.vec.Vec.index_slice_index]
        simp [alloc.vec.Vec.index_usize, hit2, List.getElem?_set, hit]
      rw [hidx2]; simp only [bind_ok, Std.uncurry]
      obtain ⟨kc, hkc, hkcb⟩ := ok_of_spec (copy_spec (alloc.vec.Vec.deref kk))
      rw [hkc]; simp only [bind_ok]
      have hdrop' : it2.val.drop (i.val + 1) = ms.val.drop (i.val + 1) := by
        have := congrArg (List.drop 1) hdrop
        simp only [List.drop_drop] at this
        rw [hit2, alloc.vec.Vec.set_val_eq, List.drop_set_of_lt (by omega)]
        simpa [Nat.add_comm] using this
      have hmv : memberView (kc, dd) = memberView (ms.val[i.val]) := by
        rw [← hx, hxe]; simp [JsonptrAdaptedProofs.memberView, hkcb, deref_bytes]
      split
      next heq =>
        have hiv : i.val = idx.val := by rw [heq]
        simp only [bind_ok]
        step as ⟨i2, hi2⟩
        try simp only [↓reduceIte, Bool.false_eq_true]
        have hi2' : i2.val = i.val + 1 := by scalar_tac
        refine ⟨by scalar_tac, by simp [hit2, hlen], by rw [hi2']; exact hdrop', ?_, ?_, by scalar_tac⟩
        · rw [hi2', hacc, ← hiv, eraseIdx_take_self _ _ hi, List.eraseIdx_of_length_le (by simp)]
        · intro _; simp only [← hiv, ← hx, hxe]
      next hne =>
        have hne' : i.val ≠ idx.val := fun e => hne (by scalar_tac)
        have hal : acc.length < Usize.max := by
          have : acc.length ≤ i.val := by
            have h1 := congrArg List.length hacc
            have h2 := List.length_eraseIdx_le (ms.val.take i.val) idx.val
            have h3 : (ms.val.take i.val).length ≤ i.val := by simp
            simp only [List.length_map] at h1
            simp only [alloc.vec.Vec.length]; omega
          scalar_tac
        obtain ⟨acc2, hacc2, hav⟩ := ok_of_spec (alloc.vec.Vec.push_spec acc (kc, dd) hal)
        rw [hacc2]; simp only [bind_ok]
        step as ⟨i2, hi2⟩
        try simp only [↓reduceIte, Bool.false_eq_true]
        have hi2' : i2.val = i.val + 1 := by scalar_tac
        refine ⟨by scalar_tac, by simp [hit2, hlen], by rw [hi2']; exact hdrop', ?_, ?_, by scalar_tac⟩
        · rw [hi2', hav, List.map_append, hacc, eraseIdx_take_succ _ _ _ hi hne', List.map_append]
          simp [hmv]
        · intro h2; exact hrem (by scalar_tac)
    next hge =>
      apply (spec_ok _).mpr
      have : i.val = ms.length := by scalar_tac
      refine ⟨hrem (by omega), ?_⟩
      rw [hacc, this, List.take_length]
  · exact ⟨by simp, rfl, by simp, by simp, fun h => by simp at h⟩

theorem map_eraseIdx' {α β : Type} (f : α → β) (l : List α) (i : Nat) :
    (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih => cases i <;> simp [ih]

theorem deleteWith (doc : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (keys : List (List Nat))
    (repl : jsonptr.resolve.DocAdapted) (hr : render keys = bytes ptr) (hbound : SliceBound ptr) :
    ∃ r d', jsonptr.adapted_api.doc_mut.delete_with_adapted doc ptr repl = .ok (r, d') ∧
      (toTree d', r.map toTree) = delete Usize.max (toTree repl) (toTree doc) keys := by
  obtain ⟨sb, hsb, hm, _⟩ := splitBackAdapted ptr (by rw [ValidPtr, ← hr]; exact render_valid keys)
  rcases List.eq_nil_or_concat keys with hk | ⟨ks, last, hk⟩
  · subst hk
    rw [← hr, splitBack_render_nil] at hm
    cases sb with
    | some p => simp [opbytes] at hm
    | none =>
      refine ⟨some doc, repl, ?_, by simp [delete]⟩
      rw [jsonptr.adapted_api.doc_mut.delete_with_adapted]; simp [hsb, core.mem.replace]
  · rw [List.concat_eq_append] at hk; subst hk
    rw [← hr, splitBack_render_snoc] at hm
    cases sb with
    | none => simp [opbytes] at hm
    | some p =>
      obtain ⟨s0, s1⟩ := p
      simp [opbytes] at hm
      obtain ⟨h0, h1⟩ := hm
      have hlen := render_length_snoc ks last
      rw [hr] at hlen
      have hb1 : SliceBound s1 := by
        unfold SliceBound at hbound ⊢; rw [← bytes_length s1, h1]; rw [bytes_length] at hlen; omega
      have hb0 : SliceBound s0 := by
        unfold SliceBound at hbound ⊢; rw [← bytes_length s0, h0]; rw [bytes_length] at hlen; omega
      obtain ⟨r, back, hrm, hout, hok, herr⟩ := resolveMutAdapted doc s0 ks h0.symm hb0
      have hmodel : delete Usize.max (toTree repl) (toTree doc) (ks ++ [last]) =
          (match resolve Usize.max (toTree doc) ks with
          | .error _ => (toTree doc, none)
          | .ok (.leaf _) => (toTree doc, none)
          | .ok (.arr items) =>
            match parseIndex Usize.max (encode last) with
            | .error _ => (toTree doc, none)
            | .ok i =>
              match forLen i items.length with
              | .error _ => (toTree doc, none)
              | .ok n =>
                match items[n]? with
                | none => (toTree doc, none)
                | some old => ((replaceAt Usize.max (toTree doc) ks (.arr (items.eraseIdx n))).getD (toTree doc), some old)
          | .ok (.obj members) =>
            match lookupKey last members with
            | none => (toTree doc, none)
            | some old => ((replaceAt Usize.max (toTree doc) ks (.obj (eraseKey last members))).getD (toTree doc), some old)) := by
        unfold delete
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, List.dropLast_concat]
        rfl
      rw [hmodel, ← hout]
      rw [jsonptr.adapted_api.doc_mut.delete_with_adapted]
      simp only [hsb, bind_ok, Std.uncurry, hrm]
      cases r with
      | Err e =>
        refine ⟨none, back (.Err e), by simp, ?_⟩
        simp [resolveOutcome, herr e _ rfl]
      | Ok node =>
        obtain ⟨hsame, hrep⟩ := hok node rfl
        cases node with
        | Leaf lp =>
          refine ⟨none, back (.Ok (.Leaf lp)), by simp, ?_⟩
          simp [resolveOutcome, hsame, toTree]
        | Array v =>
          obtain ⟨ri, hri, hpi⟩ := JsonptrAdaptedProofs.fromStrAdapted s1
          rw [h1] at hpi
          cases ri with
          | Err e =>
            refine ⟨none, back (.Ok (.Array v)), by simp [hri], ?_⟩
            simp only [indexOutcome] at hpi
            simp [resolveOutcome, hsame, JsonptrAdaptedProofs.toTree_array, ← hpi]
          | Ok i =>
            simp only [indexOutcome] at hpi
            obtain ⟨r1, hr1, hp1⟩ := JsonptrAdaptedProofs.forLen_ok i (alloc.vec.Vec.len v)
            have hl : (alloc.vec.Vec.len v).val = v.val.length := by simp
            simp only [hl] at hp1
            cases r1 with
            | Err e =>
              refine ⟨none, back (.Ok (.Array v)), by simp [hri, hr1], ?_⟩
              simp [resolveOutcome, hsame, JsonptrAdaptedProofs.toTree_array, ← hpi, hp1]
            | Ok n =>
              have hn : n.val < v.length := JsonptrAdaptedProofs.forLen_ok_lt _ _ _ hp1
              obtain ⟨⟨d, w⟩, hrem, hd, hw⟩ := ok_of_spec (removeAt_spec v n hn)
              refine ⟨some d, back (.Ok (.Array w)), by simp [hri, hr1, hrem], ?_⟩
              have hrw := hrep (.Array w)
              have hg : (v.val.map toTree)[n.val]? = some (toTree (v.val[n.val]'hn)) := by simp [hn]
              rw [JsonptrAdaptedProofs.toTree_array, hw, map_eraseIdx'] at hrw
              simp only [resolveOutcome, JsonptrAdaptedProofs.toTree_array, ← hpi, hp1, List.length_map, hg]
              rw [hrw]; simp [hd]
        | Object v =>
          have hvd : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref]
          obtain ⟨kv, hkv, hkvb⟩ := ok_of_spec (decodedKey_spec s1 last h1.symm hb1)
          have hkb : bytes (alloc.vec.Vec.deref kv) = last := by rw [← hkvb]; simp [bytes, vbytes, alloc.vec.Vec.deref]
          obtain ⟨o, ho, hfp⟩ := ok_of_spec (findKey_spec (alloc.vec.Vec.deref v) (alloc.vec.Vec.deref kv))
          rw [hvd, hkb] at hfp
          cases o with
          | none =>
            refine ⟨none, back (.Ok (.Object v)), by simp [hkv, ho], ?_⟩
            simp [resolveOutcome, hsame, JsonptrAdaptedProofs.toTree_object, findPost_none _ _ hfp]
          | some i =>
            obtain ⟨p, hp, hpk, hbef⟩ := hfp
            have hfp' : FindPost v.val last (some i) := ⟨p, hp, hpk, hbef⟩
            have hil : i.val < v.length := (List.getElem?_eq_some_iff.mp hp).1
            have hpe : v.val[i.val]'hil = p := by rw [List.getElem?_eq_getElem hil] at hp; cases hp; rfl
            obtain ⟨hlk, _, hera⟩ := findPost_model v.val last (.leaf 0) i p hfp' hp
            obtain ⟨⟨d, w⟩, hrem, hd, hw⟩ := ok_of_spec (removeMember_spec v i hil)
            refine ⟨some d, back (.Ok (.Object w)), by simp [hkv, ho, hrem], ?_⟩
            have hrw := hrep (.Object w)
            rw [JsonptrAdaptedProofs.toTree_object, hw, map_eraseIdx', ← hera] at hrw
            simp only [resolveOutcome, JsonptrAdaptedProofs.toTree_object, hlk]
            rw [hrw]; simp [hd, hpe]

theorem deleteJsonAdapted : DeleteJsonContract := by
  intro doc ptr keys hr hb
  obtain ⟨r, d', h, hm⟩ := deleteWith doc ptr keys (.Leaf 0#u64) hr hb
  exact ⟨r, d', by simp [jsonptr.adapted_api.doc_mut.delete_json_adapted, h], by simpa [toTree] using hm⟩

theorem deleteTomlAdapted : DeleteTomlContract := by
  intro doc ptr keys hr hb
  obtain ⟨r, d', h, hm⟩ := deleteWith doc ptr keys (.Object (alloc.vec.Vec.new _)) hr hb
  refine ⟨r, d', by simp [jsonptr.adapted_api.doc_mut.delete_toml_adapted, h], ?_⟩
  rw [hm, JsonptrAdaptedProofs.toTree_object]; rfl

end JsonptrExtProofs
