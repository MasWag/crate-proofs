import FxhashAdapted
import Specs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace FxHash.ByteDecode

/-- The generated checked index returns exactly the requested byte. -/
theorem index_exact (bytes : Slice Std.U8) (i : Std.Usize)
    (hi : i.val < bytes.val.length) :
    Slice.index_usize bytes i = .ok (bytes.val[i.val]) := by
  simp [Slice.index_usize, List.getElem?_eq_getElem hi]

theorem fromLEBytes_toNat (bs : List Byte) :
    (BitVec.fromLEBytes bs).toNat = FxHash.Spec.decodeLittle (bs.map BitVec.toNat) := by
  induction bs with
  | nil => simp [BitVec.fromLEBytes, FxHash.Spec.decodeLittle]
  | cons b bs ih =>
    have hb : b.toNat < 256 := BitVec.isLt b
    have ht : (BitVec.fromLEBytes bs).toNat < 2 ^ (8 * bs.length) :=
      BitVec.isLt _
    have hp : 2 ^ (8 * (b :: bs).length) = 2 ^ (8 * bs.length) * 256 := by
      simp only [List.length_cons]
      convert pow_add (2 : Nat) (8 * bs.length) 8 using 1
    have hs : (BitVec.fromLEBytes bs).toNat <<< 8 <
        2 ^ (8 * (b :: bs).length) := by
      rw [Nat.shiftLeft_eq, hp]
      exact Nat.mul_lt_mul_of_pos_right ht (by decide)
    simp only [BitVec.fromLEBytes, List.map_cons, FxHash.Spec.decodeLittle,
      BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft]
    rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ (8 * (b :: bs).length))]
    rw [Nat.mod_eq_of_lt (by omega :
      (BitVec.fromLEBytes bs).toNat < 2 ^ (8 * (b :: bs).length))]
    rw [Nat.mod_eq_of_lt hs]
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by simpa using hb)]
    rw [Nat.shiftLeft_eq, ih]
    omega

theorem decode_four (b0 b1 b2 b3 : Std.U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [b0, b1, b2, b3])).bv =
      BitVec.ofNat 32 (FxHash.Spec.decodeLittle [b0.val, b1.val, b2.val, b3.val]) := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv]).toNat = _
  rw [fromLEBytes_toNat]
  simp only [List.map_cons, List.map_nil, UScalar.bv_toNat, BitVec.toNat_ofNat]
  have h0 : b0.val < 256 := by scalar_tac
  have h1 : b1.val < 256 := by scalar_tac
  have h2 : b2.val < 256 := by scalar_tac
  have h3 : b3.val < 256 := by scalar_tac
  have hbound : FxHash.Spec.decodeLittle [b0.val, b1.val, b2.val, b3.val] < 2 ^ 32 := by
    simp only [FxHash.Spec.decodeLittle, mul_zero] at *
    omega
  rw [Nat.mod_eq_of_lt hbound]

theorem decode_eight (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    (core.num.U64.from_le_bytes (Array.make 8#usize [b0, b1, b2, b3, b4, b5, b6, b7])).bv =
      BitVec.ofNat 64 (FxHash.Spec.decodeLittle [b0.val, b1.val, b2.val, b3.val, b4.val, b5.val, b6.val, b7.val]) := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv, b4.bv, b5.bv, b6.bv, b7.bv]).toNat = _
  rw [fromLEBytes_toNat]
  simp only [List.map_cons, List.map_nil, UScalar.bv_toNat, BitVec.toNat_ofNat]
  have h0 : b0.val < 256 := by scalar_tac
  have h1 : b1.val < 256 := by scalar_tac
  have h2 : b2.val < 256 := by scalar_tac
  have h3 : b3.val < 256 := by scalar_tac
  have h4 : b4.val < 256 := by scalar_tac
  have h5 : b5.val < 256 := by scalar_tac
  have h6 : b6.val < 256 := by scalar_tac
  have h7 : b7.val < 256 := by scalar_tac
  have hbound : FxHash.Spec.decodeLittle [b0.val, b1.val, b2.val, b3.val, b4.val, b5.val, b6.val, b7.val] < 2 ^ 64 := by
    simp only [FxHash.Spec.decodeLittle, mul_zero] at *
    omega
  rw [Nat.mod_eq_of_lt hbound]

/-- The four-byte word, widened for the generated 64-bit tail, has the same value. -/
theorem decode_four_widen (b0 b1 b2 b3 : Std.U8) :
    (UScalar.cast .U64
      (core.num.U32.from_le_bytes (Array.make 4#usize [b0, b1, b2, b3]))).bv =
      BitVec.ofNat 64 (FxHash.Spec.decodeLittle [b0.val, b1.val, b2.val, b3.val]) := by
  have hd : BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv] =
      BitVec.ofNat 32 (FxHash.Spec.decodeLittle [b0.val, b1.val, b2.val, b3.val]) :=
    decode_four b0 b1 b2 b3
  change BitVec.setWidth 64 (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv]) = _
  rw [hd]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  have h0 : b0.val < 256 := by scalar_tac
  have h1 : b1.val < 256 := by scalar_tac
  have h2 : b2.val < 256 := by scalar_tac
  have h3 : b3.val < 256 := by scalar_tac
  simp only [FxHash.Spec.decodeLittle, mul_zero] at *
  omega

end FxHash.ByteDecode
