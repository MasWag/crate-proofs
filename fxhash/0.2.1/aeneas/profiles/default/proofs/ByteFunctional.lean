import ByteProofs
import ByteDecode
import SpecRecurrence
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 4096
namespace FxHash.ByteFunctional
private def foldTail32 (h : BitVec 32) (bs : List Std.U8) : BitVec 32 :=
  (bs.map UScalar.val).foldl (fun s x => FxHash.Spec.mix32 s (BitVec.ofNat 32 x)) h

private def foldTail64 (h : BitVec 64) (bs : List Std.U8) : BitVec 64 :=
  (bs.map UScalar.val).foldl (fun s x => FxHash.Spec.mix64 s (BitVec.ofNat 64 x)) h

private theorem take4_vals (bs : List Std.U8) (h : 4 ≤ bs.length) :
    (bs.map UScalar.val).take 4 =
      [bs[0].val, bs[1].val, bs[2].val, bs[3].val] := by
  cases bs with
  | nil => simp at h
  | cons a bs =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      cases bs with
      | nil => simp at h
      | cons c bs =>
        cases bs with
        | nil => simp at h
        | cons d bs => simp

theorem loop1_32 (it : core.slice.iter.Iter Std.U8) (h : Std.U32) :
    ∃ out, fxhash_adapted.write32_loop1 it h = .ok out ∧
      out.bv = foldTail32 h.bv (it.slice.val.drop it.i) := by
  let target := foldTail32 h.bv (it.slice.val.drop it.i)
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : core.slice.iter.Iter Std.U8 × Std.U32) => p.1.slice.val.length - p.1.i)
    (fun p => foldTail32 p.2.bv (p.1.slice.val.drop p.1.i) = target)
    (fun out : Std.U32 => out.bv = target)
    (fun p => fxhash_adapted.write32_loop1.body p.1 p.2)
    (it,h) (by
      intro ⟨it0,h0⟩ hi0
      by_cases hi : it0.i < it0.slice.val.length
      · have hdrop := List.drop_eq_getElem_cons (l := it0.slice.val) hi
        obtain ⟨h', hh, hs⟩ := FxHashContracts.hashWord32_correct h0
          (UScalar.cast .U32 it0.slice[it0.i])
        have hn : core.slice.iter.IteratorSliceIter.next it0 =
            .ok (some it0.slice[it0.i], { it0 with i := it0.i + 1 }) := by
          simp [core.slice.iter.IteratorSliceIter.next, hi]
          rfl
        simp [fxhash_adapted.write32_loop1.body, hn, lift, hh, Aeneas.Std.WP.spec_ok]
        constructor
        · rw [hdrop] at hi0
          simp only [foldTail32, List.map_cons, List.foldl_cons] at hi0 ⊢
          rw [hs]
          have hb : (UScalar.cast .U32 it0.slice[it0.i]).bv =
              BitVec.ofNat 32 it0.slice.val[it0.i].val := by
            apply BitVec.eq_of_toNat_eq
            change (UScalar.cast .U32 it0.slice[it0.i]).val =
              it0.slice.val[it0.i].val % 2^32
            rw [U8.cast_U32_val_eq]
            have hbnd : it0.slice.val[it0.i].val < 2^32 := by scalar_tac
            exact Nat.mod_eq_of_lt hbnd |>.symm
          simp only [hb]
          exact hi0
        · omega
      · have hdrop : it0.slice.val.drop it0.i = [] :=
          List.drop_eq_nil_of_le (by omega)
        have hn := FxHash.ByteProofs.iterator_next_none it0 hi
        simp only [fxhash_adapted.write32_loop1.body, hn,  
          bind_ok]
        simpa [foldTail32, hdrop] using hi0) (by rfl)
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write32_loop1 it h)
      (fun out : Std.U32 => out.bv = target) := by
    simpa [fxhash_adapted.write32_loop1] using hloop
  cases hm : fxhash_adapted.write32_loop1 it h using Result.cases with
  | ret value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp (hm ▸ hspec)⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

theorem loop1_64 (it : core.slice.iter.Iter Std.U8) (h : Std.U64) :
    ∃ out, fxhash_adapted.write64_loop1 it h = .ok out ∧
      out.bv = foldTail64 h.bv (it.slice.val.drop it.i) := by
  let target := foldTail64 h.bv (it.slice.val.drop it.i)
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : core.slice.iter.Iter Std.U8 × Std.U64) => p.1.slice.val.length - p.1.i)
    (fun p => foldTail64 p.2.bv (p.1.slice.val.drop p.1.i) = target)
    (fun out : Std.U64 => out.bv = target)
    (fun p => fxhash_adapted.write64_loop1.body p.1 p.2)
    (it,h) (by
      intro ⟨it0,h0⟩ hi0
      by_cases hi : it0.i < it0.slice.val.length
      · have hdrop := List.drop_eq_getElem_cons (l := it0.slice.val) hi
        obtain ⟨h', hh, hs⟩ := FxHashContracts.hashWord64_correct h0
          (UScalar.cast .U64 it0.slice[it0.i])
        have hn : core.slice.iter.IteratorSliceIter.next it0 =
            .ok (some it0.slice[it0.i], { it0 with i := it0.i + 1 }) := by
          simp [core.slice.iter.IteratorSliceIter.next, hi]
          rfl
        simp [fxhash_adapted.write64_loop1.body, hn, lift, hh, Aeneas.Std.WP.spec_ok]
        constructor
        · rw [hdrop] at hi0
          simp only [foldTail64, List.map_cons, List.foldl_cons] at hi0 ⊢
          rw [hs]
          have hb : (UScalar.cast .U64 it0.slice[it0.i]).bv =
              BitVec.ofNat 64 it0.slice.val[it0.i].val := by
            apply BitVec.eq_of_toNat_eq
            change (UScalar.cast .U64 it0.slice[it0.i]).val =
              it0.slice.val[it0.i].val % 2^64
            rw [U8.cast_U64_val_eq]
            have hbnd : it0.slice.val[it0.i].val < 2^64 := by scalar_tac
            exact Nat.mod_eq_of_lt hbnd |>.symm
          simp only [hb]
          exact hi0
        · omega
      · have hdrop : it0.slice.val.drop it0.i = [] :=
          List.drop_eq_nil_of_le (by omega)
        have hn := FxHash.ByteProofs.iterator_next_none it0 hi
        simp only [fxhash_adapted.write64_loop1.body, hn,  
          bind_ok]
        simpa [foldTail64, hdrop] using hi0) (by rfl)
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write64_loop1 it h)
      (fun out : Std.U64 => out.bv = target) := by
    simpa [fxhash_adapted.write64_loop1] using hloop
  cases hm : fxhash_adapted.write64_loop1 it h using Result.cases with
  | ret value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp (hm ▸ hspec)⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

private theorem body0_32_exact (h : Std.U32) (bytes : Slice Std.U8)
    (hlen : 4 ≤ bytes.val.length) :
    ∃ h' rest, fxhash_adapted.write32_loop0.body h bytes = .ok (.cont (h', rest)) ∧
      FxHash.Spec.write32 .little h'.bv (rest.val.map UScalar.val) =
        FxHash.Spec.write32 .little h.bv (bytes.val.map UScalar.val) ∧
      rest.val.length < bytes.val.length := by
  have hi0 : (0#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi1 : (1#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi2 : (2#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi3 : (3#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have h0 := FxHash.ByteDecode.index_exact bytes 0#usize hi0
  have h1 := FxHash.ByteDecode.index_exact bytes 1#usize hi1
  have h2 := FxHash.ByteDecode.index_exact bytes 2#usize hi2
  have h3 := FxHash.ByteDecode.index_exact bytes 3#usize hi3
  let n := core.num.U32.from_le_bytes (Array.make 4#usize
    [bytes.val[0], bytes.val[1], bytes.val[2], bytes.val[3]])
  obtain ⟨h', hh, hs⟩ := FxHashContracts.hashWord32_correct h n
  let pre : Slice Std.U8 := .from (bytes.val.take 4) (by
    have hb := Slice.length_ineq bytes
    simp [List.length_take])
  let rest : Slice Std.U8 := .from (bytes.val.drop 4) (by
    have hb := Slice.length_ineq bytes
    simp [List.length_drop]; omega)
  have hsplit : core.slice.Slice.split_at bytes 4#usize = .ok (pre, rest) := by
    simp [core.slice.Slice.split_at, Slice.length, hlen, List.splitAt_eq,
      pre, rest]
  refine ⟨h', rest, ?_, ?_, ?_⟩
  · simp [fxhash_adapted.write32_loop0.body, Slice.len, hlen,
      h0,h1,h2,h3, n, hh, hsplit, lift]
  · rw [FxHash.Spec.write32_little_cons_block h.bv (bytes.val.map UScalar.val)
      (by simpa using hlen)]
    rw [hs]
    have hd := FxHash.ByteDecode.decode_four bytes.val[0] bytes.val[1]
      bytes.val[2] bytes.val[3]
    have hdecode : n.bv = BitVec.ofNat 32
        (FxHash.Spec.decodeLittle ((bytes.val.map UScalar.val).take 4)) := by
      rw [take4_vals bytes.val hlen]
      exact hd
    rw [hdecode]
    simp only [rest, Slice.from_val, List.map_drop]
  · simp only [rest, Slice.from_val, List.length_drop]
    omega


private theorem body0_64_exact (h : Std.U64) (bytes : Slice Std.U8)
    (hlen : 8 ≤ bytes.val.length) :
    ∃ h' rest, fxhash_adapted.write64_loop0.body h bytes = .ok (.cont (h', rest)) ∧
      FxHash.Spec.write64 .little h'.bv (rest.val.map UScalar.val) =
        FxHash.Spec.write64 .little h.bv (bytes.val.map UScalar.val) ∧
      rest.val.length < bytes.val.length := by
  have hi0 : (0#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi1 : (1#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi2 : (2#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi3 : (3#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have h0 := FxHash.ByteDecode.index_exact bytes 0#usize hi0
  have h1 := FxHash.ByteDecode.index_exact bytes 1#usize hi1
  have h2 := FxHash.ByteDecode.index_exact bytes 2#usize hi2
  have h3 := FxHash.ByteDecode.index_exact bytes 3#usize hi3
  have hi4 : (4#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi5 : (5#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi6 : (6#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have hi7 : (7#usize : Std.Usize).val < bytes.val.length := by norm_num; omega
  have h4 := FxHash.ByteDecode.index_exact bytes 4#usize hi4
  have h5 := FxHash.ByteDecode.index_exact bytes 5#usize hi5
  have h6 := FxHash.ByteDecode.index_exact bytes 6#usize hi6
  have h7 := FxHash.ByteDecode.index_exact bytes 7#usize hi7
  let n := core.num.U64.from_le_bytes (Array.make 8#usize
    [bytes.val[0], bytes.val[1], bytes.val[2], bytes.val[3],
     bytes.val[4], bytes.val[5], bytes.val[6], bytes.val[7]])
  obtain ⟨h', hh, hs⟩ := FxHashContracts.hashWord64_correct h n
  let pre : Slice Std.U8 := .from (bytes.val.take 8) (by
    have hb := Slice.length_ineq bytes
    simp [List.length_take])
  let rest : Slice Std.U8 := .from (bytes.val.drop 8) (by
    have hb := Slice.length_ineq bytes
    simp [List.length_drop]; omega)
  have hsplit : core.slice.Slice.split_at bytes 8#usize = .ok (pre, rest) := by
    simp [core.slice.Slice.split_at, Slice.length, hlen, List.splitAt_eq,
      pre, rest]
  refine ⟨h', rest, ?_, ?_, ?_⟩
  · simp [fxhash_adapted.write64_loop0.body, Slice.len, hlen,
      h0,h1,h2,h3,h4,h5,h6,h7, n, hh, hsplit, lift]
  · rw [FxHash.Spec.write64_little_cons_block h.bv (bytes.val.map UScalar.val)
      (by simpa using hlen)]
    rw [hs]
    have hd := FxHash.ByteDecode.decode_eight bytes.val[0] bytes.val[1]
      bytes.val[2] bytes.val[3] bytes.val[4] bytes.val[5] bytes.val[6] bytes.val[7]
    have hdecode : n.bv = BitVec.ofNat 64
        (FxHash.Spec.decodeLittle ((bytes.val.map UScalar.val).take 8)) := by
      rw [← List.map_take, FxHash.Spec.take_eight_eq_getElems bytes.val hlen]
      simp only [List.map_cons, List.map_nil]
      exact hd
    rw [hdecode]
    simp only [rest, Slice.from_val, List.map_drop]
  · simp only [rest, Slice.from_val, List.length_drop]
    omega


theorem loop0_32 (h : Std.U32) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write32_loop0 h bytes = .ok out ∧
      out.2.val.length < 4 ∧
      FxHash.Spec.write32 .little out.1.bv (out.2.val.map UScalar.val) =
        FxHash.Spec.write32 .little h.bv (bytes.val.map UScalar.val) := by
  let target := FxHash.Spec.write32 .little h.bv (bytes.val.map UScalar.val)
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : Std.U32 × Slice Std.U8) => p.2.val.length)
    (fun p => FxHash.Spec.write32 .little p.1.bv (p.2.val.map UScalar.val) = target)
    (fun p : Std.U32 × Slice Std.U8 => p.2.val.length < 4 ∧
      FxHash.Spec.write32 .little p.1.bv (p.2.val.map UScalar.val) = target)
    (fun p => fxhash_adapted.write32_loop0.body p.1 p.2)
    (h, bytes) (by
      intro ⟨h0, bs⟩ hi
      by_cases hlen : 4 ≤ bs.val.length
      · obtain ⟨h',rest,hbody,hspec,hdec⟩ := body0_32_exact h0 bs hlen
        simp [hbody, Aeneas.Std.WP.spec_ok]
        exact ⟨hspec.trans hi, hdec⟩
      · have hshort : bs.val.length < 4 := by omega
        simp [FxHash.ByteProofs.write32_loop0_body_short h0 bs hshort,
          Aeneas.Std.WP.spec_ok, hshort, hi]) (by rfl)
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write32_loop0 h bytes)
      (fun p : Std.U32 × Slice Std.U8 => p.2.val.length < 4 ∧
      FxHash.Spec.write32 .little p.1.bv (p.2.val.map UScalar.val) = target) := by
    simpa [fxhash_adapted.write32_loop0] using hloop
  cases hm : fxhash_adapted.write32_loop0 h bytes using Result.cases with
  | ret value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp (hm ▸ hspec)⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))


theorem loop0_64 (h : Std.U64) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write64_loop0 h bytes = .ok out ∧
      out.2.val.length < 8 ∧
      FxHash.Spec.write64 .little out.1.bv (out.2.val.map UScalar.val) =
        FxHash.Spec.write64 .little h.bv (bytes.val.map UScalar.val) := by
  let target := FxHash.Spec.write64 .little h.bv (bytes.val.map UScalar.val)
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : Std.U64 × Slice Std.U8) => p.2.val.length)
    (fun p => FxHash.Spec.write64 .little p.1.bv (p.2.val.map UScalar.val) = target)
    (fun p : Std.U64 × Slice Std.U8 => p.2.val.length < 8 ∧
      FxHash.Spec.write64 .little p.1.bv (p.2.val.map UScalar.val) = target)
    (fun p => fxhash_adapted.write64_loop0.body p.1 p.2)
    (h, bytes) (by
      intro ⟨h0, bs⟩ hi
      by_cases hlen : 8 ≤ bs.val.length
      · obtain ⟨h',rest,hbody,hspec,hdec⟩ := body0_64_exact h0 bs hlen
        simp [hbody, Aeneas.Std.WP.spec_ok]
        exact ⟨hspec.trans hi, hdec⟩
      · have hshort : bs.val.length < 8 := by omega
        simp [FxHash.ByteProofs.write64_loop0_body_short h0 bs hshort,
          Aeneas.Std.WP.spec_ok, hshort, hi]) (by rfl)
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write64_loop0 h bytes)
      (fun p : Std.U64 × Slice Std.U8 => p.2.val.length < 8 ∧
      FxHash.Spec.write64 .little p.1.bv (p.2.val.map UScalar.val) = target) := by
    simpa [fxhash_adapted.write64_loop0] using hloop
  cases hm : fxhash_adapted.write64_loop0 h bytes using Result.cases with
  | ret value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp (hm ▸ hspec)⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))


theorem write32_exact (h : Std.U32) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write32 h bytes = .ok out ∧
      out.bv = FxHash.Spec.write32 .little h.bv (bytes.val.map UScalar.val) := by
  obtain ⟨⟨h1,rest⟩,hloop,hlen,hspec⟩ := loop0_32 h bytes
  obtain ⟨out,hout,hfold⟩ := loop1_32 ⟨rest,0⟩ h1
  refine ⟨out, ?_, ?_⟩
  · simp [fxhash_adapted.write32, hloop,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, hout]
  · rw [← hspec]
    rw [FxHash.Spec.write32_little_short h1.bv (rest.val.map UScalar.val)
      (by simpa using hlen)]
    simpa [foldTail32] using hfold


theorem write64_exact (h : Std.U64) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write64 h bytes = .ok out ∧
      out.bv = FxHash.Spec.write64 .little h.bv (bytes.val.map UScalar.val) := by
  obtain ⟨⟨h1,rest⟩,hloop,hlen,hspec⟩ := loop0_64 h bytes
  by_cases h4 : 4 ≤ rest.val.length
  · have hi0 : (0#usize : Std.Usize).val < rest.val.length := by norm_num; omega
    have hi1 : (1#usize : Std.Usize).val < rest.val.length := by norm_num; omega
    have hi2 : (2#usize : Std.Usize).val < rest.val.length := by norm_num; omega
    have hi3 : (3#usize : Std.Usize).val < rest.val.length := by norm_num; omega
    have h0 := FxHash.ByteDecode.index_exact rest 0#usize hi0
    have h1' := FxHash.ByteDecode.index_exact rest 1#usize hi1
    have h2 := FxHash.ByteDecode.index_exact rest 2#usize hi2
    have h3 := FxHash.ByteDecode.index_exact rest 3#usize hi3
    let n := core.num.U32.from_le_bytes (Array.make 4#usize
      [rest.val[0], rest.val[1], rest.val[2], rest.val[3]])
    obtain ⟨hnext,hh,hs⟩ := FxHashContracts.hashWord64_correct h1 (UScalar.cast .U64 n)
    let pre : Slice Std.U8 := .from (rest.val.take 4) (by
      have hb := Slice.length_ineq rest
      simp [List.length_take])
    let suff : Slice Std.U8 := .from (rest.val.drop 4) (by
      have hb := Slice.length_ineq rest
      simp [List.length_drop]; omega)
    have hsplit : core.slice.Slice.split_at rest 4#usize = .ok (pre,suff) := by
      simp [core.slice.Slice.split_at, Slice.length, h4, List.splitAt_eq, pre,suff]
    obtain ⟨out,hout,hfold⟩ := loop1_64 ⟨suff,0⟩ hnext
    refine ⟨out, ?_, ?_⟩
    · simp [fxhash_adapted.write64, hloop, h4, h0,h1',h2,h3,
        n,hh,hsplit, SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
        hout, lift]
    · rw [←hspec]
      rw [FxHash.Spec.write64_little_short h1.bv (rest.val.map UScalar.val)
        (by simpa using hlen)]
      simp only [List.length_map, h4, ↓reduceIte]
      have hd := FxHash.ByteDecode.decode_four_widen rest.val[0] rest.val[1]
        rest.val[2] rest.val[3]
      have hdecode : (UScalar.cast .U64 n).bv = BitVec.ofNat 64
          (FxHash.Spec.decodeLittle ((rest.val.map UScalar.val).take 4)) := by
        rw [←List.map_take, FxHash.Spec.take_four_eq_getElems rest.val h4]
        simpa [n] using hd
      rw [← hdecode, ← hs]
      simpa [foldTail64, suff, List.map_drop] using hfold
  · obtain ⟨out,hout,hfold⟩ := loop1_64 ⟨rest,0⟩ h1
    refine ⟨out, ?_, ?_⟩
    · simp [fxhash_adapted.write64, hloop, h4,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, hout]
    · rw [←hspec]
      rw [FxHash.Spec.write64_little_short h1.bv (rest.val.map UScalar.val)
        (by simpa using hlen)]
      simp only [List.length_map, h4, ↓reduceIte]
      simpa [foldTail64] using hfold

end FxHash.ByteFunctional
