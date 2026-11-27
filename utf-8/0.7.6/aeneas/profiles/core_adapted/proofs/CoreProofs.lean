import Utf8Core
open Aeneas Aeneas.Std Result
open Aeneas.Std.WP
namespace CoreProofs

def overwritten (b x : List U8) (n k : Nat) := b.take n ++ x.take k ++ b.drop (n+k)

theorem overwritten_step (b x : List U8) (n j : Nat) (hn : n ≤ b.length)
    (hj : j < x.length) (hb : n+j < b.length) :
    (overwritten b x n j).set (n+j) x[j] = overwritten b x n (j+1) := by
  have hp : (b.take n ++ x.take j).length = n+j := by simp [List.length_take, Nat.min_eq_left hn, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hq : (b.drop (n+j)).length > 0 := by simp; omega
  unfold overwritten
  rw [List.set_append_right _ _ (by omega)]
  rw [hp]
  simp only [Nat.sub_self]
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hq]
  simp only [List.take_zero, List.nil_append, List.drop_drop]
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.append_assoc, List.singleton_append, Nat.add_assoc]


def copyAt (input : Slice U8) (n k j : Usize) (a : Array U8 4#usize) : Result (Array U8 4#usize) := do
  if j < k then
    let byte ← Slice.index_usize input j
    let idx ← n + j
    Array.update a idx byte
  else ok a

@[step] theorem copyAt_spec (input : Slice U8) (n k j : Usize) (a : Array U8 4#usize)
    (b : List U8) (blen : b.length = 4) (bound : n.val+k.val ≤ 4)
    (inputbound : k.val ≤ input.val.length)
    (before : a.val = overwritten b input.val n.val (min k.val j.val)) :
    copyAt input n k j a ⦃ out => out.val = overwritten b input.val n.val (min k.val (j.val+1)) ⦄ := by
  unfold copyAt
  split
  · next active =>
    have jbound : j.val < input.val.length := by scalar_tac
    have nbound : n.val ≤ b.length := by omega
    have ibound : n.val+j.val < b.length := by scalar_tac
    have jm : min k.val j.val = j.val := by scalar_tac
    have j1m : min k.val (j.val+1) = j.val+1 := by scalar_tac
    step as ⟨byte, hbyte⟩
    step as ⟨idx, hidx⟩
    step as ⟨updated, hupdated⟩
    rw [hupdated, Array.set_val_eq, before, jm, j1m, hidx]
    simpa [hbyte] using overwritten_step b input.val n.val j.val nbound jbound ibound
  · next inactive =>
    have jm : min k.val j.val = k.val := by scalar_tac
    have j1m : min k.val (j.val+1) = k.val := by scalar_tac
    simpa only [spec_ok, jm, j1m] using before

@[step] theorem min_spec (a b : Usize) :
    core.cmp.min core.cmp.OrdUsize a b ⦃ out => out.val = min a.val b.val ⦄ := by
  simp only [core.cmp.min, liftFun2, core.cmp.impls.OrdUsize.min]
  split <;> simp only [spec_ok]
  · next h => have : b.val ≤ a.val := by scalar_tac
              exact (Nat.min_eq_right this).symm
  · next h => have : a.val ≤ b.val := by scalar_tac
              exact (Nat.min_eq_left this).symm

theorem splice_decomposition (s : utf8.Incomplete) (input : Slice U8) :
    s.splice_prefix input = (do
      let n ← lift (UScalar.cast .Usize s.buffer_len)
      let available ← 4#usize - n
      let k ← core.cmp.min core.cmp.OrdUsize available input.len
      let a ← copyAt input n k 0#usize s.buffer
      let a1 ← copyAt input n k 1#usize a
      let a2 ← copyAt input n k 2#usize a1
      let a3 ← copyAt input n k 3#usize a2
      ok ((n,k), {s with buffer := a3})) := by
  unfold utf8.Incomplete.splice_prefix copyAt
  simp only [bind_assoc]
  congr 1
  funext n
  congr 1
  funext available
  congr 1
  funext k
  congr 1
  funext a
  congr 1
  funext a1
  congr 1
  funext a2
  split <;> simp [bind_assoc]

@[step] theorem splice_prefix_spec (s : utf8.Incomplete) (input : Slice U8)
    (bounded : s.buffer_len.val ≤ 4) :
    s.splice_prefix input ⦃ pair =>
      pair.1.1.val = s.buffer_len.val ∧
      pair.1.2.val = min (4-s.buffer_len.val) input.val.length ∧
      pair.2.buffer_len = s.buffer_len ∧
      pair.2.buffer.val = overwritten s.buffer.val input.val s.buffer_len.val pair.1.2.val ⦄ := by
  rw [splice_decomposition]
  have castBound : s.buffer_len.val ≤ UScalar.max .Usize := by scalar_tac
  step with UScalar.cast_inBounds_spec .Usize s.buffer_len castBound as ⟨n, hn⟩
  step as ⟨available, havail⟩
  step as ⟨k, hk⟩
  have blen : s.buffer.val.length = 4 := by simp
  have sumBound : n.val+k.val ≤ 4 := by scalar_tac
  have inputBound : k.val ≤ input.val.length := by scalar_tac
  have before : s.buffer.val = overwritten s.buffer.val input.val n.val (min k.val (0#usize).val) := by
    simp [overwritten]
  step with copyAt_spec input n k 0#usize s.buffer s.buffer.val blen sumBound inputBound before as ⟨a, ha⟩
  step with copyAt_spec input n k 1#usize a s.buffer.val blen sumBound inputBound (by simpa using ha) as ⟨a1, ha1⟩
  step with copyAt_spec input n k 2#usize a1 s.buffer.val blen sumBound inputBound (by simpa using ha1) as ⟨a2, ha2⟩
  step with copyAt_spec input n k 3#usize a2 s.buffer.val blen sumBound inputBound (by simpa using ha2) as ⟨a3, ha3⟩
  refine ⟨hn, ?_, ?_⟩
  · rw [hk, havail, hn]
    rfl
  · have kb : k.val ≤ 4 := by omega
    simpa only [hn, Nat.min_eq_left kb] using ha3

theorem total_of_spec {α} (m : Result α) (p : α → Prop)
    (h : spec m p) : ∃ out, m = .ok out ∧ p out := by
  induction m using Result.cases with
  | ret x => exact ⟨x, rfl, (spec_ok x).mp h⟩
  | vis e k => simp only [spec_vis] at h
  | div => simp only [spec_div] at h

theorem splice_prefix_total (s : utf8.Incomplete) (input : Slice U8)
    (bounded : s.buffer_len.val ≤ 4) :
    ∃ out, s.splice_prefix input = .ok out ∧
      out.1.1.val = s.buffer_len.val ∧
      out.1.2.val = min (4-s.buffer_len.val) input.val.length ∧
      out.2.buffer_len = s.buffer_len ∧
      out.2.buffer.val = s.buffer.val.take s.buffer_len.val ++
        input.val.take out.1.2.val ++ s.buffer.val.drop (s.buffer_len.val+out.1.2.val) := by
  exact total_of_spec _ _ (splice_prefix_spec s input bounded)

end CoreProofs
