import ConcreteWriters.Funs
import ProofsSIntSliceEncode
import ProofsSIntFixedWrite

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open leb128fmt.sliceProof

namespace leb128fmt_writer_model

private def signedOps {T E : Type}
    (eq : core.cmp.PartialEq T T) (mask : core.ops.bit.BitAnd T T T)
    (shift : core.ops.bit.Shr T U32 T) (shiftAssign : core.ops.bit.ShrAssign T U32)
    (fromByte : core.convert.From T I8) (signed : leb128fmt.SInt T)
    (narrow : core.convert.TryFrom U8 T E) : SignedGuardOps T E where
  eq := eq
  mask := mask
  shift := ⟨shift.shr⟩
  shiftAssign := ⟨shiftAssign.shr_assign⟩
  fromSignedByte := fromByte
  integer := ⟨signed.BITS, ⟨⟩⟩
  narrow := narrow

private theorem signedWriterCorrespondence {T E : Type}
    (eq : core.cmp.PartialEq T T) (mask : core.ops.bit.BitAnd T T T)
    (shift : core.ops.bit.Shr T U32 T) (shiftAssign : core.ops.bit.ShrAssign T U32)
    (fromByte : core.convert.From T I8) (signed : leb128fmt.SInt T)
    (narrow : core.convert.TryFrom U8 T E)
    (width : U32) (value : T) (bytes : Slice U8) (start : Usize) :
    let ops := signedOps eq mask shift shiftAssign fromByte signed narrow
    leb128fmt.encode_sint_slice width eq mask shift shiftAssign fromByte signed eq narrow value bytes start =
      _root_.leb128fmt.encode_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
        ops.fromSignedByte ops.integer ops.eq ops.narrow value bytes start := by
  rfl

private theorem signedFixedCorrespondence {T E : Type}
    (eq : core.cmp.PartialEq T T) (mask : core.ops.bit.BitAnd T T T)
    (shift : core.ops.bit.Shr T U32 T) (shiftAssign : core.ops.bit.ShrAssign T U32)
    (fromByte : core.convert.From T I8) (signed : leb128fmt.SInt T)
    (narrow : core.convert.TryFrom U8 T E)
    (width : U32) (value : T) (bytes : Slice U8) (start : Usize) :
    let ops := signedOps eq mask shift shiftAssign fromByte signed narrow
    leb128fmt.encode_fixed_sint_slice width eq mask shift shiftAssign fromByte signed eq narrow
        value bytes start =
      _root_.leb128fmt.encode_fixed_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
        ops.fromSignedByte ops.integer ops.eq ops.narrow value bytes start := by
  rfl

private theorem signedMaskValue {ty : IScalarTy} (hwidth : 8 ≤ ty.numBits)
    (value mask : IScalar ty) (hmask : mask.val = 127) :
    (value &&& mask).val = value.val % 128 := by
  have hmod : (256 : Nat) ≤ 2^ty.numBits := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hwidth
  have hm : mask.bv = BitVec.ofInt ty.numBits 127 := by
    change mask.bv.toInt = 127 at hmask
    rw [← hmask, BitVec.ofInt_toInt]
  have hmNat : mask.bv.toNat = 127 := by
    rw [hm, BitVec.toNat_ofInt]
    change ((127 : Int) % (2^ty.numBits : Nat)).toNat = _
    rw [Int.emod_eq_of_lt (by decide) (by exact_mod_cast (show (127 : Nat) < 2^ty.numBits by omega))]
    rfl
  rw [IScalar.val, IScalar.bv_and, BitVec.toInt_and, hmNat]
  rw [show value.bv.toNat &&& 127 = value.bv.toNat % 128 from Nat.and_two_pow_sub_one_eq_mod _ 7]
  have hf : (128 : Int) ∣ (2^ty.numBits : Nat) := by
    exact_mod_cast (Nat.pow_dvd_pow 2 (show 7 ≤ ty.numBits by omega))
  have hb : ((value.bv.toNat % 128 : Nat) : Int) < ((2^ty.numBits+1) / 2 : Nat) := by
    exact_mod_cast (show value.bv.toNat % 128 < (2^ty.numBits+1) / 2 by omega)
  have hm' : ((value.bv.toNat % 128 : Nat) : Int) % (2^ty.numBits : Nat) =
      (value.bv.toNat % 128 : Nat) := by
    apply Int.emod_eq_of_lt (by positivity)
    exact_mod_cast (show value.bv.toNat % 128 < 2^ty.numBits by omega)
  rw [Int.bmod_eq_emod_of_lt (by rw [hm']; exact hb), hm', Int.natCast_emod]
  change (value.bv.toNat : Int) % 128 = value.bv.toInt % 128
  rw [BitVec.toInt_eq_toNat_bmod]
  calc
    _ = ((value.bv.toNat : Int) % (2^ty.numBits : Nat)) % 128 :=
      (Int.emod_emod_of_dvd _ hf).symm
    _ = ((value.bv.toNat : Int).bmod (2^ty.numBits) % (2^ty.numBits : Nat)) % 128 := by
      rw [Int.bmod_emod]
    _ = _ := Int.emod_emod_of_dvd _ hf

private theorem signedCastByte {ty : IScalarTy} (value : IScalar ty)
    (hlo : 0 ≤ value.val) (hhi : value.val < 128) :
    ((IScalar.hcast .U8 value).val : Int) = value.val := by
  rw [IScalar.hcast_val_eq]
  change ((value.val % 256).toNat : Int) = value.val
  rw [Int.emod_eq_of_lt hlo (by omega), Int.toNat_of_nonneg hlo]

private theorem signedLaws {ty : IScalarTy} {E : Type} (hwidth : 8 ≤ ty.numBits)
    (ops : SignedGuardOps (IScalar ty) E)
    (hbits : ∃ bits, ops.integer.BITS = ok bits ∧ bits.val = ty.numBits)
    (hFrom : ∀ b : I8, ∃ x, ops.fromSignedByte.«from» b = ok x ∧ x.val = b.val)
    (hShift : ∀ x n, ops.shift.shr x n = (x >>> n))
    (hNe : ∀ x y, ops.eq.ne x y = ok (decide (x ≠ y)))
    (hEq : ∀ x y, ops.eq.eq x y = ok (decide (x = y)))
    (hMask : ∀ x y, ops.mask.bitand x y = ok (x &&& y))
    (hAssign : ∀ x n, ops.shiftAssign.shr_assign x n = (x >>> n))
    (hNarrow : ∀ x, 0 ≤ x.val → x.val < 128 →
      ops.narrow.try_from x = ok (.Ok (IScalar.hcast .U8 x))) :
    SignedWriterLaws ops (IScalar.val (ty := ty)) ty.numBits := by
  have equality (x y : IScalar ty) : (x = y) ↔ x.val = y.val :=
    ⟨fun h => congrArg IScalar.val h, IScalar.eq_imp x y⟩
  constructor
  · constructor
    · exact hbits
    · exact hFrom
    · intro x n hn
      rw [hShift]
      obtain ⟨result, hr, hv, _⟩ := successful_result (IScalar.ShiftRight_spec x n hn)
      exact ⟨result, hr, by simp [hv, Int.shiftRight_eq_div_pow]⟩
    · intro x y
      rw [hNe]
      by_cases he : x.val = y.val
      · simp [(equality x y).mpr he]
      · simp [he, mt (equality x y).mp he]
  · intro x y
    rw [hEq]
    by_cases he : x.val = y.val
    · simp [(equality x y).mpr he]
    · simp [he, mt (equality x y).mp he]
  · intro x mask hm
    exact ⟨x &&& mask, hMask x mask, signedMaskValue hwidth x mask hm⟩
  · intro x
    rw [hAssign]
    have hn : (7#u32).val < ty.numBits := by change 7 < ty.numBits; omega
    obtain ⟨result, hr, hv, _⟩ := successful_result (IScalar.ShiftRight_spec x 7#u32 hn)
    exact ⟨result, hr, by rw [hv, Int.shiftRight_eq_div_pow]; rfl⟩
  · intro x hlo hhi
    exact ⟨IScalar.hcast .U8 x, hNarrow x hlo hhi, signedCastByte x hlo hhi⟩

private def signedOps8 : SignedGuardOps I8 core.num.error.TryFromIntError :=
  signedOps core.cmp.PartialEqI8 I8.Insts.CoreOpsBitBitAndI8I8
    I8.Insts.CoreOpsBitShrU32I8 I8.Insts.CoreOpsBitShrAssignU32
    (core.convert.FromSame I8) I8.Insts.Leb128fmtSInt U8.Insts.CoreConvertTryFromI8TryFromIntError

private theorem signedLaws8 : SignedWriterLaws signedOps8 IScalar.val 8 := by
  apply signedLaws (ty := .I8) (by decide)
  · exact ⟨I8.Insts.Leb128fmtSInt.BITS, rfl, by rw [I8.Insts.Leb128fmtSInt.BITS]; rfl⟩
  · intro b
    refine ⟨_, rfl, ?_⟩
    rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hlo hhi
    have ha : x ≥ 0#i8 := hlo
    simp [lift, signedOps, signedOps8,
      U8.Insts.CoreConvertTryFromI8TryFromIntError.try_from, ha]

private def signedOps16 : SignedGuardOps I16 core.num.error.TryFromIntError :=
  signedOps core.cmp.PartialEqI16 I16.Insts.CoreOpsBitBitAndI16I16
    I16.Insts.CoreOpsBitShrU32I16 I16.Insts.CoreOpsBitShrAssignU32
    core.convert.FromI16I8 I16.Insts.Leb128fmtSInt U8.Insts.CoreConvertTryFromI16TryFromIntError

private theorem signedLaws16 : SignedWriterLaws signedOps16 IScalar.val 16 := by
  apply signedLaws (ty := .I16) (by decide)
  · exact ⟨I16.Insts.Leb128fmtSInt.BITS, rfl, by rw [I16.Insts.Leb128fmtSInt.BITS]; rfl⟩
  · intro b
    refine ⟨_, rfl, ?_⟩
    exact core.convert.num.FromI16I8.from_val_eq b
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hlo hhi
    have hneg : ¬x < 0#i16 := by exact not_lt_of_ge hlo
    have htop : ¬x > 255#i16 := by
      change ¬255 < x.val
      omega
    simp [lift, signedOps, signedOps16, U8.Insts.CoreConvertTryFromI16TryFromIntError.try_from, hneg, htop]

private def signedOps32 : SignedGuardOps I32 core.num.error.TryFromIntError :=
  signedOps core.cmp.PartialEqI32 I32.Insts.CoreOpsBitBitAndI32I32
    I32.Insts.CoreOpsBitShrU32I32 I32.Insts.CoreOpsBitShrAssignU32
    core.convert.FromI32I8 I32.Insts.Leb128fmtSInt U8.Insts.CoreConvertTryFromI32TryFromIntError

private theorem signedLaws32 : SignedWriterLaws signedOps32 IScalar.val 32 := by
  apply signedLaws (ty := .I32) (by decide)
  · exact ⟨I32.Insts.Leb128fmtSInt.BITS, rfl, by rw [I32.Insts.Leb128fmtSInt.BITS]; rfl⟩
  · intro b
    refine ⟨_, rfl, ?_⟩
    exact core.convert.num.FromI32I8.from_val_eq b
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hlo hhi
    have hneg : ¬x < 0#i32 := by exact not_lt_of_ge hlo
    have htop : ¬x > 255#i32 := by
      change ¬255 < x.val
      omega
    simp [lift, signedOps, signedOps32, U8.Insts.CoreConvertTryFromI32TryFromIntError.try_from, hneg, htop]

private def signedOps64 : SignedGuardOps I64 core.num.error.TryFromIntError :=
  signedOps core.cmp.PartialEqI64 I64.Insts.CoreOpsBitBitAndI64I64
    I64.Insts.CoreOpsBitShrU32I64 I64.Insts.CoreOpsBitShrAssignU32
    core.convert.FromI64I8 I64.Insts.Leb128fmtSInt U8.Insts.CoreConvertTryFromI64TryFromIntError

private theorem signedLaws64 : SignedWriterLaws signedOps64 IScalar.val 64 := by
  apply signedLaws (ty := .I64) (by decide)
  · exact ⟨I64.Insts.Leb128fmtSInt.BITS, rfl, by rw [I64.Insts.Leb128fmtSInt.BITS]; rfl⟩
  · intro b
    refine ⟨_, rfl, ?_⟩
    exact core.convert.num.FromI64I8.from_val_eq b
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hlo hhi
    have hneg : ¬x < 0#i64 := by exact not_lt_of_ge hlo
    have htop : ¬x > 255#i64 := by
      change ¬255 < x.val
      omega
    simp [lift, signedOps, signedOps64, U8.Insts.CoreConvertTryFromI64TryFromIntError.try_from, hneg, htop]

private def signedOps128 : SignedGuardOps I128 core.num.error.TryFromIntError :=
  signedOps core.cmp.PartialEqI128 I128.Insts.CoreOpsBitBitAndI128I128
    I128.Insts.CoreOpsBitShrU32I128 I128.Insts.CoreOpsBitShrAssignU32
    core.convert.FromI128I8 I128.Insts.Leb128fmtSInt U8.Insts.CoreConvertTryFromI128TryFromIntError

private theorem signedLaws128 : SignedWriterLaws signedOps128 IScalar.val 128 := by
  apply signedLaws (ty := .I128) (by decide)
  · exact ⟨I128.Insts.Leb128fmtSInt.BITS, rfl, by rw [I128.Insts.Leb128fmtSInt.BITS]; rfl⟩
  · intro b
    refine ⟨_, rfl, ?_⟩
    exact core.convert.num.FromI128I8.from_val_eq b
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hlo hhi
    have hneg : ¬x < 0#i128 := by exact not_lt_of_ge hlo
    have htop : ¬x > 255#i128 := by
      change ¬255 < x.val
      omega
    simp [lift, signedOps, signedOps128, U8.Insts.CoreConvertTryFromI128TryFromIntError.try_from, hneg, htop]

theorem i8_writer_spec (width : U32) (value : I8) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) :
    ∃ out, i8_writer width value before start = ok out ∧
      SignedShortestPost 8 width.val value.val before start out := by
  rw [i8_writer, signedWriterCorrespondence]
  exact encode_sint_slice_spec signedOps8 IScalar.val 8 signedLaws8 width value before start hstart

theorem i8_fixed_spec (width : U32) (value : I8) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (hwidth : width.val ≤ 8)
    (hfit : SignedGuardAccepts 8 width.val value.val →
      start.val + (width.val+6)/7 ≤ before.val.length →
      SignedFits value.val ((width.val+6)/7-1)) :
    ∃ out, i8_fixed width value before start = ok out ∧
      (if SignedGuardAccepts 8 width.val value.val
        then SignedFixedWriterPost width.val value.val before start out
        else out = (none, before, start)) := by
  rw [i8_fixed, signedFixedCorrespondence]
  exact encode_fixed_sint_slice_spec signedOps8 IScalar.val 8 signedLaws8
    width value before start hstart hw hwidth hfit

theorem i16_writer_spec (width : U32) (value : I16) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) :
    ∃ out, i16_writer width value before start = ok out ∧
      SignedShortestPost 16 width.val value.val before start out := by
  rw [i16_writer, signedWriterCorrespondence]
  exact encode_sint_slice_spec signedOps16 IScalar.val 16 signedLaws16 width value before start hstart

theorem i16_fixed_spec (width : U32) (value : I16) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (hwidth : width.val ≤ 16)
    (hfit : SignedGuardAccepts 16 width.val value.val →
      start.val + (width.val+6)/7 ≤ before.val.length →
      SignedFits value.val ((width.val+6)/7-1)) :
    ∃ out, i16_fixed width value before start = ok out ∧
      (if SignedGuardAccepts 16 width.val value.val
        then SignedFixedWriterPost width.val value.val before start out
        else out = (none, before, start)) := by
  rw [i16_fixed, signedFixedCorrespondence]
  exact encode_fixed_sint_slice_spec signedOps16 IScalar.val 16 signedLaws16
    width value before start hstart hw hwidth hfit

theorem i32_writer_spec (width : U32) (value : I32) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) :
    ∃ out, i32_writer width value before start = ok out ∧
      SignedShortestPost 32 width.val value.val before start out := by
  rw [i32_writer, signedWriterCorrespondence]
  exact encode_sint_slice_spec signedOps32 IScalar.val 32 signedLaws32 width value before start hstart

theorem i32_fixed_spec (width : U32) (value : I32) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (hwidth : width.val ≤ 32)
    (hfit : SignedGuardAccepts 32 width.val value.val →
      start.val + (width.val+6)/7 ≤ before.val.length →
      SignedFits value.val ((width.val+6)/7-1)) :
    ∃ out, i32_fixed width value before start = ok out ∧
      (if SignedGuardAccepts 32 width.val value.val
        then SignedFixedWriterPost width.val value.val before start out
        else out = (none, before, start)) := by
  rw [i32_fixed, signedFixedCorrespondence]
  exact encode_fixed_sint_slice_spec signedOps32 IScalar.val 32 signedLaws32
    width value before start hstart hw hwidth hfit

theorem i64_writer_spec (width : U32) (value : I64) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) :
    ∃ out, i64_writer width value before start = ok out ∧
      SignedShortestPost 64 width.val value.val before start out := by
  rw [i64_writer, signedWriterCorrespondence]
  exact encode_sint_slice_spec signedOps64 IScalar.val 64 signedLaws64 width value before start hstart

theorem i64_fixed_spec (width : U32) (value : I64) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (hwidth : width.val ≤ 64)
    (hfit : SignedGuardAccepts 64 width.val value.val →
      start.val + (width.val+6)/7 ≤ before.val.length →
      SignedFits value.val ((width.val+6)/7-1)) :
    ∃ out, i64_fixed width value before start = ok out ∧
      (if SignedGuardAccepts 64 width.val value.val
        then SignedFixedWriterPost width.val value.val before start out
        else out = (none, before, start)) := by
  rw [i64_fixed, signedFixedCorrespondence]
  exact encode_fixed_sint_slice_spec signedOps64 IScalar.val 64 signedLaws64
    width value before start hstart hw hwidth hfit

theorem i128_writer_spec (width : U32) (value : I128) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) :
    ∃ out, i128_writer width value before start = ok out ∧
      SignedShortestPost 128 width.val value.val before start out := by
  rw [i128_writer, signedWriterCorrespondence]
  exact encode_sint_slice_spec signedOps128 IScalar.val 128 signedLaws128 width value before start hstart

theorem i128_fixed_spec (width : U32) (value : I128) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (hwidth : width.val ≤ 128)
    (hfit : SignedGuardAccepts 128 width.val value.val →
      start.val + (width.val+6)/7 ≤ before.val.length →
      SignedFits value.val ((width.val+6)/7-1)) :
    ∃ out, i128_fixed width value before start = ok out ∧
      (if SignedGuardAccepts 128 width.val value.val
        then SignedFixedWriterPost width.val value.val before start out
        else out = (none, before, start)) := by
  rw [i128_fixed, signedFixedCorrespondence]
  exact encode_fixed_sint_slice_spec signedOps128 IScalar.val 128 signedLaws128
    width value before start hstart hw hwidth hfit

end leb128fmt_writer_model
