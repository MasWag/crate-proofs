import FxhashAdapted
import Specs
import Contracts

open Aeneas Aeneas.Std Result ControlFlow Error

namespace FxHash.ByteProofs

/-- Every in-range generated slice index succeeds. -/
theorem index_succeeds (bytes : Slice Std.U8) (i : Std.Usize)
    (hi : i.val < bytes.val.length) :
    ∃ b, Slice.index_usize bytes i = .ok b := by
  have hspec := Slice.index_usize_spec bytes i (by simpa [Slice.length] using hi)
  cases hm : Slice.index_usize bytes i using Result.cases with
  | ret b => exact ⟨b, rfl⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

theorem write32_loop0_body_short (h : Std.U32) (bytes : Slice Std.U8)
    (hlen : bytes.val.length < 4) :
    fxhash_adapted.write32_loop0.body h bytes = .ok (.done (h, bytes)) := by
  simp [fxhash_adapted.write32_loop0.body, Slice.len, hlen]

theorem write64_loop0_body_short (h : Std.U64) (bytes : Slice Std.U8)
    (hlen : bytes.val.length < 8) :
    fxhash_adapted.write64_loop0.body h bytes = .ok (.done (h, bytes)) := by
  simp [fxhash_adapted.write64_loop0.body, Slice.len, hlen]

theorem write32_loop0_body_long (h : Std.U32) (bytes : Slice Std.U8)
    (hlen : 4 ≤ bytes.val.length) :
    ∃ h' rest, fxhash_adapted.write32_loop0.body h bytes = .ok (.cont (h', rest)) ∧
      rest.val = bytes.val.drop 4 ∧ rest.val.length < bytes.val.length := by
  obtain ⟨b0, h0⟩ := index_succeeds bytes 0#usize (by norm_num at *; omega)
  obtain ⟨b1, h1⟩ := index_succeeds bytes 1#usize (by norm_num at *; omega)
  obtain ⟨b2, h2⟩ := index_succeeds bytes 2#usize (by norm_num at *; omega)
  obtain ⟨b3, h3⟩ := index_succeeds bytes 3#usize (by norm_num at *; omega)
  let n := core.num.U32.from_le_bytes (Array.make 4#usize [b0, b1, b2, b3])
  obtain ⟨h', hh, _⟩ := FxHashContracts.hashWord32_correct h n
  dsimp [n] at hh
  have hs : (4#usize : Std.Usize) ≤ bytes.length := by simpa [Slice.length] using hlen
  simp [fxhash_adapted.write32_loop0.body, Slice.len, hlen, h0, h1, h2, h3,
    lift, hh,
    core.slice.Slice.split_at, List.splitAt_eq, List.length_drop]
  omega

theorem write64_loop0_body_long (h : Std.U64) (bytes : Slice Std.U8)
    (hlen : 8 ≤ bytes.val.length) :
    ∃ h' rest, fxhash_adapted.write64_loop0.body h bytes = .ok (.cont (h', rest)) ∧
      rest.val = bytes.val.drop 8 ∧ rest.val.length < bytes.val.length := by
  obtain ⟨b0, h0⟩ := index_succeeds bytes 0#usize (by norm_num at *; omega)
  obtain ⟨b1, h1⟩ := index_succeeds bytes 1#usize (by norm_num at *; omega)
  obtain ⟨b2, h2⟩ := index_succeeds bytes 2#usize (by norm_num at *; omega)
  obtain ⟨b3, h3⟩ := index_succeeds bytes 3#usize (by norm_num at *; omega)
  obtain ⟨b4, h4⟩ := index_succeeds bytes 4#usize (by norm_num at *; omega)
  obtain ⟨b5, h5⟩ := index_succeeds bytes 5#usize (by norm_num at *; omega)
  obtain ⟨b6, h6⟩ := index_succeeds bytes 6#usize (by norm_num at *; omega)
  obtain ⟨b7, h7⟩ := index_succeeds bytes 7#usize (by norm_num at *; omega)
  let n := core.num.U64.from_le_bytes (Array.make 8#usize [b0, b1, b2, b3, b4, b5, b6, b7])
  obtain ⟨h', hh, _⟩ := FxHashContracts.hashWord64_correct h n
  dsimp [n] at hh
  have hs : (8#usize : Std.Usize) ≤ bytes.length := by simpa [Slice.length] using hlen
  simp [fxhash_adapted.write64_loop0.body, Slice.len, hlen, h0, h1, h2, h3,
    h4, h5, h6, h7, lift, hh,
    core.slice.Slice.split_at, List.splitAt_eq, List.length_drop]
  omega

theorem write32_loop0_succeeds (h : Std.U32) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write32_loop0 h bytes = .ok out ∧ out.2.val.length < 4 := by
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : Std.U32 × Slice Std.U8) => p.2.val.length)
    (fun _ => True) (fun p => p.2.val.length < 4)
    (fun p => fxhash_adapted.write32_loop0.body p.1 p.2)
    (h, bytes) (by
      intro ⟨h0, bs⟩ _
      by_cases hlen : 4 ≤ bs.val.length
      · obtain ⟨h', rest, heq, _, hdec⟩ := write32_loop0_body_long h0 bs hlen
        simp [heq, hdec, Aeneas.Std.WP.spec_ok]
      · have hshort : bs.val.length < 4 := by omega
        simp [write32_loop0_body_short h0 bs hshort, Aeneas.Std.WP.spec_ok, hshort]) trivial
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write32_loop0 h bytes)
      (fun p => p.2.val.length < 4) := by
    simpa [fxhash_adapted.write32_loop0] using hloop
  cases hm : fxhash_adapted.write32_loop0 h bytes using Result.cases with
  | ret value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp (hm ▸ hspec)⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

theorem write64_loop0_succeeds (h : Std.U64) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write64_loop0 h bytes = .ok out ∧ out.2.val.length < 8 := by
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : Std.U64 × Slice Std.U8) => p.2.val.length)
    (fun _ => True) (fun p => p.2.val.length < 8)
    (fun p => fxhash_adapted.write64_loop0.body p.1 p.2)
    (h, bytes) (by
      intro ⟨h0, bs⟩ _
      by_cases hlen : 8 ≤ bs.val.length
      · obtain ⟨h', rest, heq, _, hdec⟩ := write64_loop0_body_long h0 bs hlen
        simp [heq, hdec, Aeneas.Std.WP.spec_ok]
      · have hshort : bs.val.length < 8 := by omega
        simp [write64_loop0_body_short h0 bs hshort, Aeneas.Std.WP.spec_ok, hshort]) trivial
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write64_loop0 h bytes)
      (fun p => p.2.val.length < 8) := by
    simpa [fxhash_adapted.write64_loop0] using hloop
  cases hm : fxhash_adapted.write64_loop0 h bytes using Result.cases with
  | ret value => exact ⟨value, rfl, (Aeneas.Std.WP.spec_ok value).mp (hm ▸ hspec)⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

theorem iterator_next_some (it : core.slice.iter.Iter Std.U8)
    (hi : it.i < it.slice.val.length) :
    ∃ b it', core.slice.iter.IteratorSliceIter.next it = .ok (some b, it') ∧
      it'.slice.val.length - it'.i < it.slice.val.length - it.i := by
  simp [core.slice.iter.IteratorSliceIter.next, hi]
  omega

theorem iterator_next_none (it : core.slice.iter.Iter Std.U8)
    (hi : ¬ it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it = .ok (none, it) := by
  simp [core.slice.iter.IteratorSliceIter.next, hi]

theorem write32_loop1_succeeds (it : core.slice.iter.Iter Std.U8) (h : Std.U32) :
    ∃ out, fxhash_adapted.write32_loop1 it h = .ok out := by
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : core.slice.iter.Iter Std.U8 × Std.U32) => p.1.slice.val.length - p.1.i)
    (fun _ => True) (fun _ => True)
    (fun p => fxhash_adapted.write32_loop1.body p.1 p.2)
    (it, h) (by
      intro ⟨it0, h0⟩ _
      by_cases hi : it0.i < it0.slice.val.length
      · obtain ⟨b, it', hn, hdec⟩ := iterator_next_some it0 hi
        obtain ⟨h', hh, _⟩ := FxHashContracts.hashWord32_correct h0 (UScalar.cast .U32 b)
        simp [fxhash_adapted.write32_loop1.body, hn, hh, lift, hdec]
      · simp [fxhash_adapted.write32_loop1.body, iterator_next_none it0 hi]) trivial
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write32_loop1 it h) (fun _ => True) := by
    simpa [fxhash_adapted.write32_loop1] using hloop
  cases hm : fxhash_adapted.write32_loop1 it h using Result.cases with
  | ret value => exact ⟨value, rfl⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

theorem write64_loop1_succeeds (it : core.slice.iter.Iter Std.U8) (h : Std.U64) :
    ∃ out, fxhash_adapted.write64_loop1 it h = .ok out := by
  have hloop := Aeneas.Std.loop.spec_decr_nat
    (fun (p : core.slice.iter.Iter Std.U8 × Std.U64) => p.1.slice.val.length - p.1.i)
    (fun _ => True) (fun _ => True)
    (fun p => fxhash_adapted.write64_loop1.body p.1 p.2)
    (it, h) (by
      intro ⟨it0, h0⟩ _
      by_cases hi : it0.i < it0.slice.val.length
      · obtain ⟨b, it', hn, hdec⟩ := iterator_next_some it0 hi
        obtain ⟨h', hh, _⟩ := FxHashContracts.hashWord64_correct h0 (UScalar.cast .U64 b)
        simp [fxhash_adapted.write64_loop1.body, hn, hh, lift, hdec]
      · simp [fxhash_adapted.write64_loop1.body, iterator_next_none it0 hi]) trivial
  have hspec : Aeneas.Std.WP.spec (fxhash_adapted.write64_loop1 it h) (fun _ => True) := by
    simpa [fxhash_adapted.write64_loop1] using hloop
  cases hm : fxhash_adapted.write64_loop1 it h using Result.cases with
  | ret value => exact ⟨value, rfl⟩
  | vis effect k => exact False.elim ((Aeneas.Std.WP.spec_vis effect k).mp (hm ▸ hspec))
  | div => exact False.elim (Aeneas.Std.WP.spec_div.mp (hm ▸ hspec))

theorem write32_succeeds (h : Std.U32) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write32 h bytes = .ok out := by
  obtain ⟨⟨h', rest⟩, hloop, _⟩ := write32_loop0_succeeds h bytes
  obtain ⟨out, hout⟩ := write32_loop1_succeeds ⟨rest, 0⟩ h'
  exact ⟨out, by simp [fxhash_adapted.write32, hloop,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, hout]⟩

theorem write64_succeeds (h : Std.U64) (bytes : Slice Std.U8) :
    ∃ out, fxhash_adapted.write64 h bytes = .ok out := by
  obtain ⟨⟨h', rest⟩, hloop, _⟩ := write64_loop0_succeeds h bytes
  by_cases h4 : 4 ≤ rest.val.length
  · obtain ⟨b0, h0⟩ := index_succeeds rest 0#usize (by norm_num at *; omega)
    obtain ⟨b1, h1⟩ := index_succeeds rest 1#usize (by norm_num at *; omega)
    obtain ⟨b2, h2⟩ := index_succeeds rest 2#usize (by norm_num at *; omega)
    obtain ⟨b3, h3⟩ := index_succeeds rest 3#usize (by norm_num at *; omega)
    let n := core.num.U32.from_le_bytes (Array.make 4#usize [b0, b1, b2, b3])
    obtain ⟨h'', hh, _⟩ := FxHashContracts.hashWord64_correct h' (UScalar.cast .U64 n)
    dsimp [n] at hh
    have hs : (4#usize : Std.Usize) ≤ rest.length := by simpa [Slice.length] using h4
    obtain ⟨pair, hsplit⟩ : ∃ pair, core.slice.Slice.split_at rest 4#usize = .ok pair := by
      simp [core.slice.Slice.split_at, h4]
    rcases pair with ⟨pre, suf⟩
    obtain ⟨out, hout⟩ := write64_loop1_succeeds ⟨suf, 0⟩ h''
    exact ⟨out, by simp [fxhash_adapted.write64, hloop, h4, h0, h1, h2, h3, hsplit,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
      lift, hh, hout]⟩
  · obtain ⟨out, hout⟩ := write64_loop1_succeeds ⟨rest, 0⟩ h'
    exact ⟨out, by simp [fxhash_adapted.write64, hloop, h4,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, hout]⟩

theorem decode_one (b : Std.U8) :
    (BitVec.fromLEBytes [b.bv]).toNat = FxHash.Spec.decodeLittle [b.val] := by
  simp [BitVec.fromLEBytes, FxHash.Spec.decodeLittle]

theorem decode_two (b c : Std.U8) :
    (BitVec.fromLEBytes [b.bv, c.bv]).toNat =
      FxHash.Spec.decodeLittle [b.val, c.val] := by
  simp [BitVec.fromLEBytes, FxHash.Spec.decodeLittle]
  have hb : b.val < 256 := by scalar_tac
  have hc : c.val < 256 := by scalar_tac
  have hmodb : b.val % 65536 = b.val := Nat.mod_eq_of_lt (by omega)
  have hmodc : c.val % 65536 = c.val := Nat.mod_eq_of_lt (by omega)
  rw [hmodb, hmodc]
  have hmodshift : (c.val <<< 8) % 65536 = c.val <<< 8 :=
    Nat.mod_eq_of_lt (by simp [Nat.shiftLeft_eq]; omega)
  rw [hmodshift, Nat.or_comm]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by simpa using hb) c.val]
  simp [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm]

end FxHash.ByteProofs
