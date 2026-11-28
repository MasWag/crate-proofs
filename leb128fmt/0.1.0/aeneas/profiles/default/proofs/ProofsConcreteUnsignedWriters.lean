import ConcreteWriters.Funs
import ProofsUIntFixedWrite

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open leb128fmt.sliceProof

namespace leb128fmt.writerProof

private def unsignedOps {T E : Type}
    (eq : core.cmp.PartialEq T T) (and : core.ops.bit.BitAnd T T T)
    (shr : leb128fmt_writer_model.core.ops.bit.Shr T U32 T)
    (shrAssign : leb128fmt_writer_model.core.ops.bit.ShrAssign T U32)
    (fromByte : core.convert.From T U8) (width : leb128fmt_writer_model.leb128fmt.UInt T)
    (convert : core.convert.TryFrom U8 T E) : UIntWriterOps T E where
  eq := eq
  and := and
  shr := ⟨shr.shr⟩
  shrAssign := ⟨shrAssign.shr_assign⟩
  fromByteTrait := fromByte
  type := ⟨width.BITS, {}⟩
  convert := convert

theorem writer_max_len_eq (width : U32) :
    leb128fmt_writer_model.leb128fmt.max_len width = _root_.leb128fmt.max_len width := by
  rfl

private theorem unsigned_transfer {T E : Type}
    (eq : core.cmp.PartialEq T T) (and : core.ops.bit.BitAnd T T T)
    (shr : leb128fmt_writer_model.core.ops.bit.Shr T U32 T)
    (shrAssign : leb128fmt_writer_model.core.ops.bit.ShrAssign T U32)
    (fromByte : core.convert.From T U8) (size : leb128fmt_writer_model.leb128fmt.UInt T)
    (convert : core.convert.TryFrom U8 T E) (val : T → Nat) (storage : Nat)
    (laws : UIntWriterLaws (unsignedOps eq and shr shrAssign fromByte size convert) val storage)
    (width : U32) (value : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ storage) :
    (∃ out, leb128fmt_writer_model.leb128fmt.encode_uint_slice width eq and shr shrAssign
        fromByte size eq convert value before start = ok out ∧
      UIntWriterPost width.val (val value) before start out) ∧
    (0 < width.val → ∃ out, leb128fmt_writer_model.leb128fmt.encode_fixed_uint_slice width
        and shr shrAssign fromByte size eq convert value before start = ok out ∧
      UIntFixedWriterPost width.val (val value) before start out) := by
  constructor
  · exact encode_uint_slice_spec _ _ _ laws width value before start hstart hwidth
  · intro hpositive
    exact encode_fixed_uint_slice_spec _ _ _ laws width value before start hstart hwidth hpositive

private theorem unsigned_scalar_writer_laws {ty : UScalarTy} {E : Type}
    (op : UIntWriterOps (UScalar ty) E) (hwidth : 7 < ty.numBits)
    (hsize : ∃ bits, op.type.BITS = ok bits ∧ bits.val = ty.numBits)
    (hfrom : ∀ b : U8, ∃ out, op.fromByteTrait.«from» b = ok out ∧ out.val = b.val)
    (hand : ∀ x m, op.and.bitand x m = ok (x &&& m))
    (hshr : ∀ (x : UScalar ty) (n : U32), op.shr.shr x n = (x >>> n))
    (hshrAssign : ∀ x : UScalar ty, op.shrAssign.shr_assign x 7#u32 = (x >>> (7#u32)))
    (heq : ∀ x y, op.eq.eq x y = ok (decide (x = y)))
    (hne : ∀ x y, op.eq.ne x y = ok (decide (x ≠ y)))
    (hnarrow : ∀ x, x.val < 256 → op.convert.try_from x = ok (.Ok (UScalar.cast .U8 x))) :
    UIntWriterLaws op UScalar.val ty.numBits := by
  constructor
  · exact hsize
  · intro x
    exact x.bv.isLt
  · exact hfrom
  · intro x mask hm
    refine ⟨x &&& mask, hand _ _, ?_⟩
    rw [UScalar.val_and, hm]
    exact Nat.and_two_pow_sub_one_eq_mod x.val 7
  · intro x n hn
    obtain ⟨out, hr, hv, _⟩ := total_result (UScalar.ShiftRight_spec x n hn)
    exact ⟨out, (hshr x n).trans hr, hv.trans (Nat.shiftRight_eq_div_pow _ _)⟩
  · intro x
    obtain ⟨out, hr, hv, _⟩ := total_result (UScalar.ShiftRight_spec x 7#u32 hwidth)
    exact ⟨out, (hshrAssign x).trans hr, hv.trans (Nat.shiftRight_eq_div_pow _ _)⟩
  · intro x y
    rw [heq]
    by_cases h : x.val = y.val
    · simp [UScalar.eq_imp x y h]
    · have hn : x ≠ y := fun hh => h (congrArg UScalar.val hh)
      simp [h, hn]
  · intro x y
    rw [hne]
    by_cases h : x.val = y.val
    · simp [UScalar.eq_imp x y h]
    · have hn : x ≠ y := fun hh => h (congrArg UScalar.val hh)
      simp [h, hn]
  · intro x h
    refine ⟨UScalar.cast .U8 x, hnarrow x h, ?_⟩
    rw [UScalar.cast_val_eq]
    change x.val % 256 = x.val
    exact Nat.mod_eq_of_lt h


open leb128fmt_writer_model


private def u16Ops : UIntWriterOps U16 core.num.error.TryFromIntError :=
  unsignedOps core.cmp.PartialEqU16 U16.Insts.CoreOpsBitBitAndU16U16
    U16.Insts.CoreOpsBitShrU32U16 U16.Insts.CoreOpsBitShrAssignU32
    core.convert.FromU16U8 U16.Insts.Leb128fmtUInt U8.Insts.CoreConvertTryFromU16TryFromIntError

private theorem u16Laws : UIntWriterLaws u16Ops (UScalar.val (ty := .U16)) 16 := by
  apply unsigned_scalar_writer_laws
  · decide
  · exact ⟨U16.Insts.Leb128fmtUInt.BITS, rfl, by rw [U16.Insts.Leb128fmtUInt.BITS]; rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU16U8.from b, rfl, core.convert.num.FromU16U8.from_val_eq b⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hx
    change U8.Insts.CoreConvertTryFromU16TryFromIntError.try_from x = _
    have hbound : ¬ (255 < x.val) := by omega
    simp [U8.Insts.CoreConvertTryFromU16TryFromIntError.try_from, hbound, lift]

theorem u16_writer_spec (width : U32) (value : U16) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 16) :
    ∃ out, u16_writer width value before start = ok out ∧
      UIntWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u16Laws width value before start hstart hwidth).1

theorem u16_fixed_spec (width : U32) (value : U16) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 16)
    (hpositive : 0 < width.val) :
    ∃ out, u16_fixed width value before start = ok out ∧
      UIntFixedWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u16Laws width value before start hstart hwidth).2 hpositive


private def u32Ops : UIntWriterOps U32 core.num.error.TryFromIntError :=
  unsignedOps core.cmp.PartialEqU32 U32.Insts.CoreOpsBitBitAndU32U32
    U32.Insts.CoreOpsBitShrU32U32 U32.Insts.CoreOpsBitShrAssignU32
    core.convert.FromU32U8 U32.Insts.Leb128fmtUInt U8.Insts.CoreConvertTryFromU32TryFromIntError

private theorem u32Laws : UIntWriterLaws u32Ops (UScalar.val (ty := .U32)) 32 := by
  apply unsigned_scalar_writer_laws
  · decide
  · exact ⟨U32.Insts.Leb128fmtUInt.BITS, rfl, by rw [U32.Insts.Leb128fmtUInt.BITS]; rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU32U8.from b, rfl, core.convert.num.FromU32U8.from_val_eq b⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hx
    change U8.Insts.CoreConvertTryFromU32TryFromIntError.try_from x = _
    have hbound : ¬ (255 < x.val) := by omega
    simp [U8.Insts.CoreConvertTryFromU32TryFromIntError.try_from, hbound, lift]

theorem u32_writer_spec (width : U32) (value : U32) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 32) :
    ∃ out, u32_writer width value before start = ok out ∧
      UIntWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u32Laws width value before start hstart hwidth).1

theorem u32_fixed_spec (width : U32) (value : U32) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 32)
    (hpositive : 0 < width.val) :
    ∃ out, u32_fixed width value before start = ok out ∧
      UIntFixedWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u32Laws width value before start hstart hwidth).2 hpositive


private def u64Ops : UIntWriterOps U64 core.num.error.TryFromIntError :=
  unsignedOps core.cmp.PartialEqU64 U64.Insts.CoreOpsBitBitAndU64U64
    U64.Insts.CoreOpsBitShrU32U64 U64.Insts.CoreOpsBitShrAssignU32
    core.convert.FromU64U8 U64.Insts.Leb128fmtUInt U8.Insts.CoreConvertTryFromU64TryFromIntError

private theorem u64Laws : UIntWriterLaws u64Ops (UScalar.val (ty := .U64)) 64 := by
  apply unsigned_scalar_writer_laws
  · decide
  · exact ⟨U64.Insts.Leb128fmtUInt.BITS, rfl, by rw [U64.Insts.Leb128fmtUInt.BITS]; rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU64U8.from b, rfl, core.convert.num.FromU64U8.from_val_eq b⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hx
    change U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from x = _
    have hbound : ¬ (255 < x.val) := by omega
    simp [U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from, hbound, lift]

theorem u64_writer_spec (width : U32) (value : U64) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 64) :
    ∃ out, u64_writer width value before start = ok out ∧
      UIntWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u64Laws width value before start hstart hwidth).1

theorem u64_fixed_spec (width : U32) (value : U64) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 64)
    (hpositive : 0 < width.val) :
    ∃ out, u64_fixed width value before start = ok out ∧
      UIntFixedWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u64Laws width value before start hstart hwidth).2 hpositive


private def u128Ops : UIntWriterOps U128 core.num.error.TryFromIntError :=
  unsignedOps core.cmp.PartialEqU128 U128.Insts.CoreOpsBitBitAndU128U128
    U128.Insts.CoreOpsBitShrU32U128 U128.Insts.CoreOpsBitShrAssignU32
    core.convert.FromU128U8 U128.Insts.Leb128fmtUInt U8.Insts.CoreConvertTryFromU128TryFromIntError

private theorem u128Laws : UIntWriterLaws u128Ops (UScalar.val (ty := .U128)) 128 := by
  apply unsigned_scalar_writer_laws
  · decide
  · exact ⟨U128.Insts.Leb128fmtUInt.BITS, rfl, by rw [U128.Insts.Leb128fmtUInt.BITS]; rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU128U8.from b, rfl, core.convert.num.FromU128U8.from_val_eq b⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro x hx
    change U8.Insts.CoreConvertTryFromU128TryFromIntError.try_from x = _
    have hbound : ¬ (255 < x.val) := by omega
    simp [U8.Insts.CoreConvertTryFromU128TryFromIntError.try_from, hbound, lift]

theorem u128_writer_spec (width : U32) (value : U128) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 128) :
    ∃ out, u128_writer width value before start = ok out ∧
      UIntWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u128Laws width value before start hstart hwidth).1

theorem u128_fixed_spec (width : U32) (value : U128) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 128)
    (hpositive : 0 < width.val) :
    ∃ out, u128_fixed width value before start = ok out ∧
      UIntFixedWriterPost width.val value.val before start out :=
  (unsigned_transfer _ _ _ _ _ _ _ _ _ u128Laws width value before start hstart hwidth).2 hpositive

end leb128fmt.writerProof
