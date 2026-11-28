import ProofsUIntSliceEncode
import LebProofs

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open leb128fmt_slice_probe

namespace leb128fmt.sliceProof

def fixedUnsignedByte (value count index : Nat) : Nat :=
  value / 128^index % 128 + if index+1 < count then 128 else 0

def UIntFixedWriterPost (width value : Nat) (before : Slice U8) (start : Usize)
    (out : Option Usize × Slice U8 × Usize) : Prop :=
  let count := (width+6)/7
  if value < 2^width ∧ start.val + count ≤ before.val.length then
    ∃ written, out.1 = some written ∧ written.val = count ∧
      out.2.2.val = start.val + count ∧
      SliceWritten (fixedUnsignedByte value count) before start.val count out.2.1
  else out = (none, before, start)

private def FixedUIntLoopInv {T : Type} (val : T → Nat) (value count : Nat)
    (before : Slice U8) (start : Usize)
    (state : core.ops.range.Range Usize × T × Slice U8 × Usize) : Prop :=
  state.1.end.val + 1 = count ∧
  state.1.start.val < count ∧
  state.2.2.2.val = start.val + state.1.start.val ∧
  val state.2.1 = value / 128 ^ state.1.start.val ∧
  SliceWritten (fixedUnsignedByte value count) before start.val state.1.start.val state.2.2.1

private def FixedUIntLoopPost (value count : Nat) (before : Slice U8) (start : Usize)
    (out : Usize × Slice U8 × Usize) : Prop :=
  out.1.val = count ∧ out.2.2.val = start.val + count ∧
    SliceWritten (fixedUnsignedByte value count) before start.val count out.2.1

private theorem fixed_uint_loop_spec {T E : Type} (op : UIntWriterOps T E) (val : T → Nat)
    (storage : Nat) (laws : UIntWriterLaws op val storage) (value : T)
    (before : Slice U8) (start stop : Usize) (count : Nat)
    (hstop : stop.val + 1 = count) (hspace : start.val + count ≤ before.val.length) :
    WP.spec (leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice_loop0
      op.and op.shrAssign op.fromByteTrait op.convert
      { start := 0#usize, «end» := stop } value before start start)
      (FixedUIntLoopPost (val value) count before start) := by
  unfold leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice_loop0
  apply loop.spec_decr_nat (measure := fun state => count - state.1.start.val)
    (inv := FixedUIntLoopInv val (val value) count before start)
  · rintro ⟨iter, rest, out, idx⟩ ⟨hend, hiter, hidx, hrest, hwrite⟩
    dsimp at *
    have hlimit : idx.val < before.val.length := by omega
    have hlen := hwrite.1
    obtain ⟨mask, hmask, hm⟩ := laws.fromByte 127#u8
    obtain ⟨digit, hmasking, hd⟩ := laws.lowMask rest mask hm
    have hdigit : val digit < 128 := by rw [hd]; exact Nat.mod_lt _ (by decide)
    obtain ⟨byte, hconvert, hb⟩ := laws.narrow digit (by omega)
    unfold leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice_loop0.body
    by_cases hmore : iter.start.val < iter.end.val
    · apply WP.spec_bind (core.iter.range.IteratorRange.next_Usize_some_spec iter hmore)
      rintro ⟨o, iter1⟩ ⟨rfl, hiter1, hiterEnd⟩
      obtain ⟨next, hshift, hnext⟩ := laws.lowShift rest
      simp [hmask, hmasking, hconvert, hshift]
      step*
      have hbyte : (byte ||| 128#u8).val =
          fixedUnsignedByte (val value) count iter.start.val := by
        have ht : byte.val < 128 := hb.symm ▸ hdigit
        simp only [UScalar.val_or, fixedUnsignedByte, ite_eq_left (by omega : iter.start.val+1 < count)]
        change byte.val ||| 128 = _
        rw [Nat.or_two_pow_eq_add_of_lt (n := 7) ht, hb, hd, hrest]
      have hbytes : SliceWritten (fixedUnsignedByte (val value) count) before start.val
          (idx.val-start.val) out := by
        rw [show idx.val-start.val = iter.start.val by omega]
        exact hwrite
      have happend := written_append (b := b1) (by omega : start.val ≤ idx.val) hlimit hbytes
      have hbNext := happend (by simpa only [b1_post, show idx.val-start.val = iter.start.val by omega] using hbyte)
      simp only [FixedUIntLoopInv, s_post, index1_post]
      refine ⟨⟨by simpa [hiterEnd] using hend, by omega, by omega, ?_, ?_⟩, by omega⟩
      · rw [hnext, hrest, Nat.div_div_eq_div_mul, hiter1, Nat.pow_succ]
      · rw [show iter1.start.val = idx.val + 1 - start.val by omega]
        exact hbNext
    · apply WP.spec_bind (core.iter.range.IteratorRange.next_Usize_none_spec iter (Nat.le_of_not_gt hmore))
      rintro ⟨o, iter1⟩ ⟨rfl, heq⟩
      subst iter1
      simp [hmask, hmasking, hconvert]
      step*
      have hbyte : byte.val = fixedUnsignedByte (val value) count iter.start.val := by
        simp [fixedUnsignedByte, hb, hd, hrest, show ¬iter.start.val+1 < count by omega]
      have hbytes : SliceWritten (fixedUnsignedByte (val value) count) before start.val
          (idx.val-start.val) out := by
        rw [show idx.val-start.val = iter.start.val by omega]
        exact hwrite
      have happend := written_append (b := byte) (by omega : start.val ≤ idx.val) hlimit hbytes
      have hbNext := happend (by simpa only [show idx.val-start.val = iter.start.val by omega] using hbyte)
      simp only [FixedUIntLoopPost, output1_post]
      refine ⟨by omega, by omega, ?_⟩
      rw [show idx.val+1-start.val = count by omega] at hbNext
      exact hbNext
  · refine ⟨hstop, ?_, by simp, by simp, ?_⟩
    · change 0 < count
      omega
    · exact written_zero (fixedUnsignedByte (val value) count) before start.val

private theorem fixedLoopSame {T E : Type} (op : UIntWriterOps T E)
    (iter : core.ops.range.Range Usize) (value : T) (output : Slice U8) (start index : Usize) :
    leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice_loop1 op.and op.shrAssign
      op.fromByteTrait op.convert iter value output start index =
    leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice_loop0 op.and op.shrAssign
      op.fromByteTrait op.convert iter value output start index := by rfl

private theorem fixed_after_range_guard {T E : Type} (op : UIntWriterOps T E) (val : T → Nat)
    (storage : Nat) (laws : UIntWriterLaws op val storage)
    (width : U32) (value : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : 0 < width.val)
    (hfit : val value < 2^width.val) :
    WP.spec (do
      let s ← core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) before { start := start }
      let count ← leb128fmt_slice_probe.leb128fmt.max_len width
      if Slice.len s < count then ok (none, before, start)
      else
        let stop ← count - 1#usize
        let (written, out, pos) ← leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice_loop0
          op.and op.shrAssign op.fromByteTrait op.convert
          { start := 0#usize, «end» := stop } value before start start
        ok (some written, out, pos))
      (UIntFixedWriterPost width.val (val value) before start) := by
  have hslice : ({ start := start } : core.ops.range.RangeFrom Usize).start ≤ before.length := hstart
  rw [Slice.index_SliceIndexRangeFromUsizeSliceInst]
  apply WP.spec_bind (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec _ before hslice)
  intro s ⟨_, hs⟩
  obtain ⟨count, hc, hcount⟩ := _root_.leb128fmt.max_len_spec width
  change leb128fmt_slice_probe.leb128fmt.max_len width = ok count at hc
  simp only [hc, Aeneas.Std.bind_ok]
  by_cases hshort : Slice.len s < count
  · have hshort' : ¬start.val + (width.val+6)/7 ≤ before.val.length := by
      have hlt : s.val.length < count.val := hshort
      change s.val.length = before.val.length - start.val at hs
      omega
    simp [hshort, UIntFixedWriterPost, hshort']
  · have hspace : start.val + (width.val+6)/7 ≤ before.val.length := by
      have hlt : ¬s.val.length < count.val := hshort
      change s.val.length = before.val.length - start.val at hs
      omega
    rw [ite_eq_right hshort]
    have hone : 1 ≤ count.val := by omega
    step as ⟨stop, hstop, _⟩
    apply WP.spec_bind (fixed_uint_loop_spec op val storage laws value before start stop
      ((width.val+6)/7) (by omega) hspace)
    rintro ⟨written, out, pos⟩ ⟨hcount', hpos, hwrite⟩
    change WP.spec (ok (some written, out, pos)) _
    simp only [WP.spec_ok, UIntFixedWriterPost, hfit, hspace, and_self, ↓reduceIte]
    exact ⟨written, rfl, hcount', hpos, hwrite⟩

theorem encode_fixed_uint_slice_spec {T E : Type} (op : UIntWriterOps T E)
    (val : T → Nat) (storage : Nat) (laws : UIntWriterLaws op val storage)
    (width : U32) (value : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ storage)
    (hpositive : 0 < width.val) :
    ∃ out, leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice width
        op.and op.shr op.shrAssign op.fromByteTrait op.type op.eq op.convert value before start = ok out ∧
      UIntFixedWriterPost width.val (val value) before start out := by
  apply total_result
  obtain ⟨storageWidth, hstorage, hstorageVal⟩ := laws.size
  obtain ⟨zero, hzero, hzeroVal⟩ := laws.fromByte 0#u8
  have hzv : val zero = 0 := hzeroVal
  unfold leb128fmt_slice_probe.leb128fmt.encode_fixed_uint_slice
  simp [hstorage]
  by_cases hlt : width.val < storageWidth.val
  · have hsmall : width.val < storage := by omega
    obtain ⟨shifted, hshift, hshiftValue⟩ := laws.shift value width hsmall
    have hcmp := laws.unequal shifted zero
    rw [hzv, hshiftValue] at hcmp
    by_cases hfit : val value < 2^width.val
    · have hq : val value / 2^width.val = 0 := Nat.div_eq_of_lt hfit
      simpa [hlt, hshift, hzero, hcmp, hq] using
        fixed_after_range_guard op val storage laws width value before start hstart hpositive hfit
    · have hq : val value / 2^width.val ≠ 0 := by
        intro h
        exact hfit ((Nat.div_eq_zero_iff.mp h).resolve_left (by positivity))
      simp [hlt, hshift, hzero, hcmp, hq, UIntFixedWriterPost, hfit]
  · have he : width.val = storage := by omega
    have hfit : val value < 2^width.val := by rw [he]; exact laws.bounds value
    simp only [ite_eq_right hlt]
    simp only [fixedLoopSame op]
    exact fixed_after_range_guard op val storage laws width value before start hstart hpositive hfit

theorem u8_fixed_spec (width : U32) (value : U8) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hlower : 0 < width.val) (hupper : width.val ≤ 8) :
    ∃ out, u8_fixed width value before start = ok out ∧
      UIntFixedWriterPost width.val value.val before start out := by
  exact encode_fixed_uint_slice_spec u8_writer_ops (UScalar.val (ty := .U8)) 8 u8_writer_laws
    width value before start hstart hupper hlower

end leb128fmt.sliceProof
