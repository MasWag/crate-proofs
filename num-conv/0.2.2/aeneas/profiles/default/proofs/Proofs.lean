import NumConvVerificationApi
import ScalarLemmas
import Operations
open Aeneas Aeneas.Std
open num_conv_verification_api
set_option maxHeartbeats 1000000
namespace NumConvProof
theorem widen_u8_u8_spec (x : U8) :
  ∃ out, widen_u8_u8 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem extend_u8_u8_spec (x : U8) :
  ∃ out, extend_u8_u8 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_u8_u8_spec (x : U8) :
  ∃ out, truncate_u8_u8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (0) (NumConvSpec.unsignedMax 8) (x.val : Int) (out.val : Int) := by
  refine ⟨x, rfl, ?_⟩
  have hc := unsigned_cast_contract .U8 x
  simpa only [UScalarTy.numBits, UScalar.cast_val_mod_pow_greater_numBits_eq .U8 x (by omega)] using hc



theorem widen_u8_u16_spec (x : U8) :
  ∃ out, widen_u8_u16 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U16 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u8_u16_spec (x : U8) :
  ∃ out, extend_u8_u16 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U16 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u16_u8_spec (x : U16) :
  ∃ out, truncate_u16_u8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (0) (NumConvSpec.unsignedMax 8) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U8 x, rfl, unsigned_cast_contract .U8 x⟩



theorem widen_u8_u32_spec (x : U8) :
  ∃ out, widen_u8_u32 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u8_u32_spec (x : U8) :
  ∃ out, extend_u8_u32 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u32_u8_spec (x : U32) :
  ∃ out, truncate_u32_u8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (0) (NumConvSpec.unsignedMax 8) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U8 x, rfl, unsigned_cast_contract .U8 x⟩



theorem widen_u8_u64_spec (x : U8) :
  ∃ out, widen_u8_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u8_u64_spec (x : U8) :
  ∃ out, extend_u8_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u64_u8_spec (x : U64) :
  ∃ out, truncate_u64_u8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (0) (NumConvSpec.unsignedMax 8) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U8 x, rfl, unsigned_cast_contract .U8 x⟩



theorem widen_u8_u128_spec (x : U8) :
  ∃ out, widen_u8_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u8_u128_spec (x : U8) :
  ∃ out, extend_u8_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u128_u8_spec (x : U128) :
  ∃ out, truncate_u128_u8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (0) (NumConvSpec.unsignedMax 8) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U8 x, rfl, unsigned_cast_contract .U8 x⟩



theorem widen_u8_usize_spec (x : U8) :
  ∃ out, widen_u8_usize x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .Usize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .Usize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u8_usize_spec (x : U8) :
  ∃ out, extend_u8_usize x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .Usize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .Usize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_usize_u8_spec (x : Usize) :
  ∃ out, truncate_usize_u8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (0) (NumConvSpec.unsignedMax 8) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U8 x, rfl, unsigned_cast_contract .U8 x⟩



theorem widen_u16_u16_spec (x : U16) :
  ∃ out, widen_u16_u16 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem extend_u16_u16_spec (x : U16) :
  ∃ out, extend_u16_u16 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_u16_u16_spec (x : U16) :
  ∃ out, truncate_u16_u16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (0) (NumConvSpec.unsignedMax 16) (x.val : Int) (out.val : Int) := by
  refine ⟨x, rfl, ?_⟩
  have hc := unsigned_cast_contract .U16 x
  simpa only [UScalarTy.numBits, UScalar.cast_val_mod_pow_greater_numBits_eq .U16 x (by omega)] using hc



theorem widen_u16_u32_spec (x : U16) :
  ∃ out, widen_u16_u32 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u16_u32_spec (x : U16) :
  ∃ out, extend_u16_u32 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u32_u16_spec (x : U32) :
  ∃ out, truncate_u32_u16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (0) (NumConvSpec.unsignedMax 16) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U16 x, rfl, unsigned_cast_contract .U16 x⟩



theorem widen_u16_u64_spec (x : U16) :
  ∃ out, widen_u16_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u16_u64_spec (x : U16) :
  ∃ out, extend_u16_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u64_u16_spec (x : U64) :
  ∃ out, truncate_u64_u16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (0) (NumConvSpec.unsignedMax 16) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U16 x, rfl, unsigned_cast_contract .U16 x⟩



theorem widen_u16_u128_spec (x : U16) :
  ∃ out, widen_u16_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u16_u128_spec (x : U16) :
  ∃ out, extend_u16_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u128_u16_spec (x : U128) :
  ∃ out, truncate_u128_u16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (0) (NumConvSpec.unsignedMax 16) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U16 x, rfl, unsigned_cast_contract .U16 x⟩



theorem widen_u16_usize_spec (x : U16) :
  ∃ out, widen_u16_usize x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .Usize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .Usize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u16_usize_spec (x : U16) :
  ∃ out, extend_u16_usize x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .Usize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .Usize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_usize_u16_spec (x : Usize) :
  ∃ out, truncate_usize_u16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (0) (NumConvSpec.unsignedMax 16) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U16 x, rfl, unsigned_cast_contract .U16 x⟩



theorem widen_u32_u32_spec (x : U32) :
  ∃ out, widen_u32_u32 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem extend_u32_u32_spec (x : U32) :
  ∃ out, extend_u32_u32 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_u32_u32_spec (x : U32) :
  ∃ out, truncate_u32_u32 x = Result.ok out ∧ NumConvSpec.boundedCongruent 32 (0) (NumConvSpec.unsignedMax 32) (x.val : Int) (out.val : Int) := by
  refine ⟨x, rfl, ?_⟩
  have hc := unsigned_cast_contract .U32 x
  simpa only [UScalarTy.numBits, UScalar.cast_val_mod_pow_greater_numBits_eq .U32 x (by omega)] using hc



theorem widen_u32_u64_spec (x : U32) :
  ∃ out, widen_u32_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u32_u64_spec (x : U32) :
  ∃ out, extend_u32_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u64_u32_spec (x : U64) :
  ∃ out, truncate_u64_u32 x = Result.ok out ∧ NumConvSpec.boundedCongruent 32 (0) (NumConvSpec.unsignedMax 32) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U32 x, rfl, unsigned_cast_contract .U32 x⟩



theorem widen_u32_u128_spec (x : U32) :
  ∃ out, widen_u32_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u32_u128_spec (x : U32) :
  ∃ out, extend_u32_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u128_u32_spec (x : U128) :
  ∃ out, truncate_u128_u32 x = Result.ok out ∧ NumConvSpec.boundedCongruent 32 (0) (NumConvSpec.unsignedMax 32) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U32 x, rfl, unsigned_cast_contract .U32 x⟩



theorem widen_u64_u64_spec (x : U64) :
  ∃ out, widen_u64_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem extend_u64_u64_spec (x : U64) :
  ∃ out, extend_u64_u64 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_u64_u64_spec (x : U64) :
  ∃ out, truncate_u64_u64 x = Result.ok out ∧ NumConvSpec.boundedCongruent 64 (0) (NumConvSpec.unsignedMax 64) (x.val : Int) (out.val : Int) := by
  refine ⟨x, rfl, ?_⟩
  have hc := unsigned_cast_contract .U64 x
  simpa only [UScalarTy.numBits, UScalar.cast_val_mod_pow_greater_numBits_eq .U64 x (by omega)] using hc



theorem widen_u64_u128_spec (x : U64) :
  ∃ out, widen_u64_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem extend_u64_u128_spec (x : U64) :
  ∃ out, extend_u64_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  refine ⟨UScalar.cast .U128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact congrArg Int.ofNat (UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits]))

theorem truncate_u128_u64_spec (x : U128) :
  ∃ out, truncate_u128_u64 x = Result.ok out ∧ NumConvSpec.boundedCongruent 64 (0) (NumConvSpec.unsignedMax 64) (x.val : Int) (out.val : Int) := by
  exact ⟨UScalar.cast .U64 x, rfl, unsigned_cast_contract .U64 x⟩



theorem widen_u128_u128_spec (x : U128) :
  ∃ out, widen_u128_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem extend_u128_u128_spec (x : U128) :
  ∃ out, extend_u128_u128 x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_u128_u128_spec (x : U128) :
  ∃ out, truncate_u128_u128 x = Result.ok out ∧ NumConvSpec.boundedCongruent 128 (0) (NumConvSpec.unsignedMax 128) (x.val : Int) (out.val : Int) := by
  refine ⟨x, rfl, ?_⟩
  have hc := unsigned_cast_contract .U128 x
  simpa only [UScalarTy.numBits, UScalar.cast_val_mod_pow_greater_numBits_eq .U128 x (by omega)] using hc



theorem widen_usize_usize_spec (x : Usize) :
  ∃ out, widen_usize_usize x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem extend_usize_usize_spec (x : Usize) :
  ∃ out, extend_usize_usize x = Result.ok out ∧ NumConvSpec.preservesValue (x.val : Int) (out.val : Int) := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_usize_usize_spec (x : Usize) :
  ∃ out, truncate_usize_usize x = Result.ok out ∧ NumConvSpec.boundedCongruent UScalarTy.Usize.numBits (0) (NumConvSpec.unsignedMax UScalarTy.Usize.numBits) (x.val : Int) (out.val : Int) := by
  refine ⟨x, rfl, ?_⟩
  have hc := unsigned_cast_contract .Usize x
  simpa only [UScalarTy.numBits, UScalar.cast_val_mod_pow_greater_numBits_eq .Usize x (by omega)] using hc



theorem widen_i8_i8_spec (x : I8) :
  ∃ out, widen_i8_i8 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem extend_i8_i8_spec (x : I8) :
  ∃ out, extend_i8_i8 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_i8_i8_spec (x : I8) :
  ∃ out, truncate_i8_i8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val out.val := by
  refine ⟨x, rfl, ?_⟩
  have hc := signed_cast_contract .I8 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])
  simpa only [IScalarTy.numBits, IScalar.val_mod_pow_greater_numBits .I8 x (by omega)] using hc



theorem widen_i8_i16_spec (x : I8) :
  ∃ out, widen_i8_i16 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I16 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i8_i16_spec (x : I8) :
  ∃ out, extend_i8_i16 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I16 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i16_i8_spec (x : I16) :
  ∃ out, truncate_i16_i8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val out.val := by
  exact ⟨IScalar.cast .I8 x, rfl, signed_cast_contract .I8 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i8_i32_spec (x : I8) :
  ∃ out, widen_i8_i32 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i8_i32_spec (x : I8) :
  ∃ out, extend_i8_i32 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i32_i8_spec (x : I32) :
  ∃ out, truncate_i32_i8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val out.val := by
  exact ⟨IScalar.cast .I8 x, rfl, signed_cast_contract .I8 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i8_i64_spec (x : I8) :
  ∃ out, widen_i8_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i8_i64_spec (x : I8) :
  ∃ out, extend_i8_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i64_i8_spec (x : I64) :
  ∃ out, truncate_i64_i8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val out.val := by
  exact ⟨IScalar.cast .I8 x, rfl, signed_cast_contract .I8 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i8_i128_spec (x : I8) :
  ∃ out, widen_i8_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i8_i128_spec (x : I8) :
  ∃ out, extend_i8_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i128_i8_spec (x : I128) :
  ∃ out, truncate_i128_i8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val out.val := by
  exact ⟨IScalar.cast .I8 x, rfl, signed_cast_contract .I8 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i8_isize_spec (x : I8) :
  ∃ out, widen_i8_isize x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .Isize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .Isize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i8_isize_spec (x : I8) :
  ∃ out, extend_i8_isize x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .Isize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .Isize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_isize_i8_spec (x : Isize) :
  ∃ out, truncate_isize_i8 x = Result.ok out ∧ NumConvSpec.boundedCongruent 8 (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val out.val := by
  exact ⟨IScalar.cast .I8 x, rfl, signed_cast_contract .I8 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i16_i16_spec (x : I16) :
  ∃ out, widen_i16_i16 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem extend_i16_i16_spec (x : I16) :
  ∃ out, extend_i16_i16 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_i16_i16_spec (x : I16) :
  ∃ out, truncate_i16_i16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val out.val := by
  refine ⟨x, rfl, ?_⟩
  have hc := signed_cast_contract .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])
  simpa only [IScalarTy.numBits, IScalar.val_mod_pow_greater_numBits .I16 x (by omega)] using hc



theorem widen_i16_i32_spec (x : I16) :
  ∃ out, widen_i16_i32 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i16_i32_spec (x : I16) :
  ∃ out, extend_i16_i32 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I32 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i32_i16_spec (x : I32) :
  ∃ out, truncate_i32_i16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val out.val := by
  exact ⟨IScalar.cast .I16 x, rfl, signed_cast_contract .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i16_i64_spec (x : I16) :
  ∃ out, widen_i16_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i16_i64_spec (x : I16) :
  ∃ out, extend_i16_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i64_i16_spec (x : I64) :
  ∃ out, truncate_i64_i16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val out.val := by
  exact ⟨IScalar.cast .I16 x, rfl, signed_cast_contract .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i16_i128_spec (x : I16) :
  ∃ out, widen_i16_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i16_i128_spec (x : I16) :
  ∃ out, extend_i16_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i128_i16_spec (x : I128) :
  ∃ out, truncate_i128_i16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val out.val := by
  exact ⟨IScalar.cast .I16 x, rfl, signed_cast_contract .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i16_isize_spec (x : I16) :
  ∃ out, widen_i16_isize x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .Isize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .Isize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i16_isize_spec (x : I16) :
  ∃ out, extend_i16_isize x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .Isize x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .Isize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_isize_i16_spec (x : Isize) :
  ∃ out, truncate_isize_i16 x = Result.ok out ∧ NumConvSpec.boundedCongruent 16 (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val out.val := by
  exact ⟨IScalar.cast .I16 x, rfl, signed_cast_contract .I16 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i32_i32_spec (x : I32) :
  ∃ out, widen_i32_i32 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem extend_i32_i32_spec (x : I32) :
  ∃ out, extend_i32_i32 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_i32_i32_spec (x : I32) :
  ∃ out, truncate_i32_i32 x = Result.ok out ∧ NumConvSpec.boundedCongruent 32 (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val out.val := by
  refine ⟨x, rfl, ?_⟩
  have hc := signed_cast_contract .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])
  simpa only [IScalarTy.numBits, IScalar.val_mod_pow_greater_numBits .I32 x (by omega)] using hc



theorem widen_i32_i64_spec (x : I32) :
  ∃ out, widen_i32_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i32_i64_spec (x : I32) :
  ∃ out, extend_i32_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I64 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i64_i32_spec (x : I64) :
  ∃ out, truncate_i64_i32 x = Result.ok out ∧ NumConvSpec.boundedCongruent 32 (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val out.val := by
  exact ⟨IScalar.cast .I32 x, rfl, signed_cast_contract .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i32_i128_spec (x : I32) :
  ∃ out, widen_i32_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i32_i128_spec (x : I32) :
  ∃ out, extend_i32_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i128_i32_spec (x : I128) :
  ∃ out, truncate_i128_i32 x = Result.ok out ∧ NumConvSpec.boundedCongruent 32 (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val out.val := by
  exact ⟨IScalar.cast .I32 x, rfl, signed_cast_contract .I32 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i64_i64_spec (x : I64) :
  ∃ out, widen_i64_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem extend_i64_i64_spec (x : I64) :
  ∃ out, extend_i64_i64 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_i64_i64_spec (x : I64) :
  ∃ out, truncate_i64_i64 x = Result.ok out ∧ NumConvSpec.boundedCongruent 64 (NumConvSpec.signedMin 64) (NumConvSpec.signedMax 64) x.val out.val := by
  refine ⟨x, rfl, ?_⟩
  have hc := signed_cast_contract .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])
  simpa only [IScalarTy.numBits, IScalar.val_mod_pow_greater_numBits .I64 x (by omega)] using hc



theorem widen_i64_i128_spec (x : I64) :
  ∃ out, widen_i64_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem extend_i64_i128_spec (x : I64) :
  ∃ out, extend_i64_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  refine ⟨IScalar.cast .I128 x, rfl, ?_⟩
  unfold NumConvSpec.preservesValue
  exact IScalar.val_mod_pow_greater_numBits .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])

theorem truncate_i128_i64_spec (x : I128) :
  ∃ out, truncate_i128_i64 x = Result.ok out ∧ NumConvSpec.boundedCongruent 64 (NumConvSpec.signedMin 64) (NumConvSpec.signedMax 64) x.val out.val := by
  exact ⟨IScalar.cast .I64 x, rfl, signed_cast_contract .I64 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])⟩



theorem widen_i128_i128_spec (x : I128) :
  ∃ out, widen_i128_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem extend_i128_i128_spec (x : I128) :
  ∃ out, extend_i128_i128 x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_i128_i128_spec (x : I128) :
  ∃ out, truncate_i128_i128 x = Result.ok out ∧ NumConvSpec.boundedCongruent 128 (NumConvSpec.signedMin 128) (NumConvSpec.signedMax 128) x.val out.val := by
  refine ⟨x, rfl, ?_⟩
  have hc := signed_cast_contract .I128 x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])
  simpa only [IScalarTy.numBits, IScalar.val_mod_pow_greater_numBits .I128 x (by omega)] using hc



theorem widen_isize_isize_spec (x : Isize) :
  ∃ out, widen_isize_isize x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem extend_isize_isize_spec (x : Isize) :
  ∃ out, extend_isize_isize x = Result.ok out ∧ NumConvSpec.preservesValue x.val out.val := by
  exact ⟨x, rfl, rfl⟩

theorem truncate_isize_isize_spec (x : Isize) :
  ∃ out, truncate_isize_isize x = Result.ok out ∧ NumConvSpec.boundedCongruent IScalarTy.Isize.numBits (NumConvSpec.signedMin IScalarTy.Isize.numBits) (NumConvSpec.signedMax IScalarTy.Isize.numBits) x.val out.val := by
  refine ⟨x, rfl, ?_⟩
  have hc := signed_cast_contract .Isize x (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits, IScalarTy.numBits])
  simpa only [IScalarTy.numBits, IScalar.val_mod_pow_greater_numBits .Isize x (by omega)] using hc



theorem saturating_truncate_u8_u8_spec (x : U8) :
  ∃ out, saturating_truncate_u8_u8 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : saturating_truncate_u8_u8 x = unsignedSat x core.num.U8.MIN core.num.U8.MAX := by
    simp only [saturating_truncate_u8_u8, release.Truncate.Blanket.saturating_truncate,
      U8.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.saturating_truncate,
      unsignedSat, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedSat_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u8_u8_spec (x : U8) :
  ∃ out, checked_truncate_u8_u8 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : checked_truncate_u8_u8 x = unsignedChecked x core.num.U8.MIN core.num.U8.MAX := by
    simp only [checked_truncate_u8_u8, release.Truncate.Blanket.checked_truncate,
      U8.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.checked_truncate,
      unsignedChecked, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedChecked_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u16_u8_spec (x : U16) :
  ∃ out, saturating_truncate_u16_u8 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : saturating_truncate_u16_u8 x = unsignedSat x core.num.U8.MIN core.num.U8.MAX := by
    simp only [saturating_truncate_u16_u8, release.Truncate.Blanket.saturating_truncate,
      U16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedSat_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u16_u8_spec (x : U16) :
  ∃ out, checked_truncate_u16_u8 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : checked_truncate_u16_u8 x = unsignedChecked x core.num.U8.MIN core.num.U8.MAX := by
    simp only [checked_truncate_u16_u8, release.Truncate.Blanket.checked_truncate,
      U16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedChecked_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u32_u8_spec (x : U32) :
  ∃ out, saturating_truncate_u32_u8 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : saturating_truncate_u32_u8 x = unsignedSat x core.num.U8.MIN core.num.U8.MAX := by
    simp only [saturating_truncate_u32_u8, release.Truncate.Blanket.saturating_truncate,
      U32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedSat_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u32_u8_spec (x : U32) :
  ∃ out, checked_truncate_u32_u8 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : checked_truncate_u32_u8 x = unsignedChecked x core.num.U8.MIN core.num.U8.MAX := by
    simp only [checked_truncate_u32_u8, release.Truncate.Blanket.checked_truncate,
      U32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedChecked_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u64_u8_spec (x : U64) :
  ∃ out, saturating_truncate_u64_u8 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : saturating_truncate_u64_u8 x = unsignedSat x core.num.U8.MIN core.num.U8.MAX := by
    simp only [saturating_truncate_u64_u8, release.Truncate.Blanket.saturating_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedSat_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u64_u8_spec (x : U64) :
  ∃ out, checked_truncate_u64_u8 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : checked_truncate_u64_u8 x = unsignedChecked x core.num.U8.MIN core.num.U8.MAX := by
    simp only [checked_truncate_u64_u8, release.Truncate.Blanket.checked_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedChecked_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u128_u8_spec (x : U128) :
  ∃ out, saturating_truncate_u128_u8 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : saturating_truncate_u128_u8 x = unsignedSat x core.num.U8.MIN core.num.U8.MAX := by
    simp only [saturating_truncate_u128_u8, release.Truncate.Blanket.saturating_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedSat_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u128_u8_spec (x : U128) :
  ∃ out, checked_truncate_u128_u8 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : checked_truncate_u128_u8 x = unsignedChecked x core.num.U8.MIN core.num.U8.MAX := by
    simp only [checked_truncate_u128_u8, release.Truncate.Blanket.checked_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedChecked_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_usize_u8_spec (x : Usize) :
  ∃ out, saturating_truncate_usize_u8 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : saturating_truncate_usize_u8 x = unsignedSat x core.num.U8.MIN core.num.U8.MAX := by
    simp only [saturating_truncate_usize_u8, release.Truncate.Blanket.saturating_truncate,
      Usize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedSat_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_usize_u8_spec (x : Usize) :
  ∃ out, checked_truncate_usize_u8 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 8) (x.val : Int) := by
  have heq : checked_truncate_usize_u8 x = unsignedChecked x core.num.U8.MIN core.num.U8.MAX := by
    simp only [checked_truncate_usize_u8, release.Truncate.Blanket.checked_truncate,
      Usize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU8.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U8.MIN, core.num.U8.MAX, U8.rMax] using
    unsignedChecked_spec x core.num.U8.MIN core.num.U8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u16_u16_spec (x : U16) :
  ∃ out, saturating_truncate_u16_u16 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : saturating_truncate_u16_u16 x = unsignedSat x core.num.U16.MIN core.num.U16.MAX := by
    simp only [saturating_truncate_u16_u16, release.Truncate.Blanket.saturating_truncate,
      U16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.saturating_truncate,
      unsignedSat, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedSat_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u16_u16_spec (x : U16) :
  ∃ out, checked_truncate_u16_u16 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : checked_truncate_u16_u16 x = unsignedChecked x core.num.U16.MIN core.num.U16.MAX := by
    simp only [checked_truncate_u16_u16, release.Truncate.Blanket.checked_truncate,
      U16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.checked_truncate,
      unsignedChecked, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedChecked_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u32_u16_spec (x : U32) :
  ∃ out, saturating_truncate_u32_u16 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : saturating_truncate_u32_u16 x = unsignedSat x core.num.U16.MIN core.num.U16.MAX := by
    simp only [saturating_truncate_u32_u16, release.Truncate.Blanket.saturating_truncate,
      U32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedSat_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u32_u16_spec (x : U32) :
  ∃ out, checked_truncate_u32_u16 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : checked_truncate_u32_u16 x = unsignedChecked x core.num.U16.MIN core.num.U16.MAX := by
    simp only [checked_truncate_u32_u16, release.Truncate.Blanket.checked_truncate,
      U32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedChecked_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u64_u16_spec (x : U64) :
  ∃ out, saturating_truncate_u64_u16 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : saturating_truncate_u64_u16 x = unsignedSat x core.num.U16.MIN core.num.U16.MAX := by
    simp only [saturating_truncate_u64_u16, release.Truncate.Blanket.saturating_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedSat_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u64_u16_spec (x : U64) :
  ∃ out, checked_truncate_u64_u16 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : checked_truncate_u64_u16 x = unsignedChecked x core.num.U16.MIN core.num.U16.MAX := by
    simp only [checked_truncate_u64_u16, release.Truncate.Blanket.checked_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedChecked_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u128_u16_spec (x : U128) :
  ∃ out, saturating_truncate_u128_u16 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : saturating_truncate_u128_u16 x = unsignedSat x core.num.U16.MIN core.num.U16.MAX := by
    simp only [saturating_truncate_u128_u16, release.Truncate.Blanket.saturating_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedSat_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u128_u16_spec (x : U128) :
  ∃ out, checked_truncate_u128_u16 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : checked_truncate_u128_u16 x = unsignedChecked x core.num.U16.MIN core.num.U16.MAX := by
    simp only [checked_truncate_u128_u16, release.Truncate.Blanket.checked_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedChecked_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_usize_u16_spec (x : Usize) :
  ∃ out, saturating_truncate_usize_u16 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : saturating_truncate_usize_u16 x = unsignedSat x core.num.U16.MIN core.num.U16.MAX := by
    simp only [saturating_truncate_usize_u16, release.Truncate.Blanket.saturating_truncate,
      Usize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedSat_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_usize_u16_spec (x : Usize) :
  ∃ out, checked_truncate_usize_u16 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 16) (x.val : Int) := by
  have heq : checked_truncate_usize_u16 x = unsignedChecked x core.num.U16.MIN core.num.U16.MAX := by
    simp only [checked_truncate_usize_u16, release.Truncate.Blanket.checked_truncate,
      Usize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU16.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U16.MIN, core.num.U16.MAX, U16.rMax] using
    unsignedChecked_spec x core.num.U16.MIN core.num.U16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u32_u32_spec (x : U32) :
  ∃ out, saturating_truncate_u32_u32 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 32) (x.val : Int) := by
  have heq : saturating_truncate_u32_u32 x = unsignedSat x core.num.U32.MIN core.num.U32.MAX := by
    simp only [saturating_truncate_u32_u32, release.Truncate.Blanket.saturating_truncate,
      U32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU32.saturating_truncate,
      unsignedSat, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U32.MIN, core.num.U32.MAX, U32.rMax] using
    unsignedSat_spec x core.num.U32.MIN core.num.U32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u32_u32_spec (x : U32) :
  ∃ out, checked_truncate_u32_u32 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 32) (x.val : Int) := by
  have heq : checked_truncate_u32_u32 x = unsignedChecked x core.num.U32.MIN core.num.U32.MAX := by
    simp only [checked_truncate_u32_u32, release.Truncate.Blanket.checked_truncate,
      U32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU32.checked_truncate,
      unsignedChecked, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U32.MIN, core.num.U32.MAX, U32.rMax] using
    unsignedChecked_spec x core.num.U32.MIN core.num.U32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u64_u32_spec (x : U64) :
  ∃ out, saturating_truncate_u64_u32 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 32) (x.val : Int) := by
  have heq : saturating_truncate_u64_u32 x = unsignedSat x core.num.U32.MIN core.num.U32.MAX := by
    simp only [saturating_truncate_u64_u32, release.Truncate.Blanket.saturating_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU32.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U32.MIN, core.num.U32.MAX, U32.rMax] using
    unsignedSat_spec x core.num.U32.MIN core.num.U32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u64_u32_spec (x : U64) :
  ∃ out, checked_truncate_u64_u32 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 32) (x.val : Int) := by
  have heq : checked_truncate_u64_u32 x = unsignedChecked x core.num.U32.MIN core.num.U32.MAX := by
    simp only [checked_truncate_u64_u32, release.Truncate.Blanket.checked_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU32.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U32.MIN, core.num.U32.MAX, U32.rMax] using
    unsignedChecked_spec x core.num.U32.MIN core.num.U32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u128_u32_spec (x : U128) :
  ∃ out, saturating_truncate_u128_u32 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 32) (x.val : Int) := by
  have heq : saturating_truncate_u128_u32 x = unsignedSat x core.num.U32.MIN core.num.U32.MAX := by
    simp only [saturating_truncate_u128_u32, release.Truncate.Blanket.saturating_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU32.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U32.MIN, core.num.U32.MAX, U32.rMax] using
    unsignedSat_spec x core.num.U32.MIN core.num.U32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u128_u32_spec (x : U128) :
  ∃ out, checked_truncate_u128_u32 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 32) (x.val : Int) := by
  have heq : checked_truncate_u128_u32 x = unsignedChecked x core.num.U32.MIN core.num.U32.MAX := by
    simp only [checked_truncate_u128_u32, release.Truncate.Blanket.checked_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU32.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U32.MIN, core.num.U32.MAX, U32.rMax] using
    unsignedChecked_spec x core.num.U32.MIN core.num.U32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u64_u64_spec (x : U64) :
  ∃ out, saturating_truncate_u64_u64 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 64) (x.val : Int) := by
  have heq : saturating_truncate_u64_u64 x = unsignedSat x core.num.U64.MIN core.num.U64.MAX := by
    simp only [saturating_truncate_u64_u64, release.Truncate.Blanket.saturating_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU64.saturating_truncate,
      unsignedSat, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U64.MIN, core.num.U64.MAX, U64.rMax] using
    unsignedSat_spec x core.num.U64.MIN core.num.U64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u64_u64_spec (x : U64) :
  ∃ out, checked_truncate_u64_u64 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 64) (x.val : Int) := by
  have heq : checked_truncate_u64_u64 x = unsignedChecked x core.num.U64.MIN core.num.U64.MAX := by
    simp only [checked_truncate_u64_u64, release.Truncate.Blanket.checked_truncate,
      U64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU64.checked_truncate,
      unsignedChecked, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U64.MIN, core.num.U64.MAX, U64.rMax] using
    unsignedChecked_spec x core.num.U64.MIN core.num.U64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u128_u64_spec (x : U128) :
  ∃ out, saturating_truncate_u128_u64 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 64) (x.val : Int) := by
  have heq : saturating_truncate_u128_u64 x = unsignedSat x core.num.U64.MIN core.num.U64.MAX := by
    simp only [saturating_truncate_u128_u64, release.Truncate.Blanket.saturating_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU64.saturating_truncate,
      unsignedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U64.MIN, core.num.U64.MAX, U64.rMax] using
    unsignedSat_spec x core.num.U64.MIN core.num.U64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u128_u64_spec (x : U128) :
  ∃ out, checked_truncate_u128_u64 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 64) (x.val : Int) := by
  have heq : checked_truncate_u128_u64 x = unsignedChecked x core.num.U64.MIN core.num.U64.MAX := by
    simp only [checked_truncate_u128_u64, release.Truncate.Blanket.checked_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU64.checked_truncate,
      unsignedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U64.MIN, core.num.U64.MAX, U64.rMax] using
    unsignedChecked_spec x core.num.U64.MIN core.num.U64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_u128_u128_spec (x : U128) :
  ∃ out, saturating_truncate_u128_u128 x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax 128) (x.val : Int) := by
  have heq : saturating_truncate_u128_u128 x = unsignedSat x core.num.U128.MIN core.num.U128.MAX := by
    simp only [saturating_truncate_u128_u128, release.Truncate.Blanket.saturating_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU128.saturating_truncate,
      unsignedSat, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U128.MIN, core.num.U128.MAX, U128.rMax] using
    unsignedSat_spec x core.num.U128.MIN core.num.U128.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_u128_u128_spec (x : U128) :
  ∃ out, checked_truncate_u128_u128 x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax 128) (x.val : Int) := by
  have heq : checked_truncate_u128_u128 x = unsignedChecked x core.num.U128.MIN core.num.U128.MAX := by
    simp only [checked_truncate_u128_u128, release.Truncate.Blanket.checked_truncate,
      U128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedU128.checked_truncate,
      unsignedChecked, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.U128.MIN, core.num.U128.MAX, U128.rMax] using
    unsignedChecked_spec x core.num.U128.MIN core.num.U128.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_usize_usize_spec (x : Usize) :
  ∃ out, saturating_truncate_usize_usize x = Result.ok out ∧ (out.val : Int) = NumConvSpec.saturate (0) (NumConvSpec.unsignedMax UScalarTy.Usize.numBits) (x.val : Int) := by
  have heq : saturating_truncate_usize_usize x = unsignedSat x core.num.Usize.MIN core.num.Usize.MAX := by
    simp only [saturating_truncate_usize_usize, release.Truncate.Blanket.saturating_truncate,
      Usize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedUsize.saturating_truncate,
      unsignedSat, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.Usize.MIN, core.num.Usize.MAX, Usize.max, Usize.numBits, UScalar.max, UScalarTy.numBits] using
    unsignedSat_spec x core.num.Usize.MIN core.num.Usize.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_usize_usize_spec (x : Usize) :
  ∃ out, checked_truncate_usize_usize x = Result.ok out ∧ out.map (fun v => (v.val : Int)) = NumConvSpec.checked (0) (NumConvSpec.unsignedMax UScalarTy.Usize.numBits) (x.val : Int) := by
  have heq : checked_truncate_usize_usize x = unsignedChecked x core.num.Usize.MIN core.num.Usize.MAX := by
    simp only [checked_truncate_usize_usize, release.Truncate.Blanket.checked_truncate,
      Usize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedUsize.checked_truncate,
      unsignedChecked, unsignedCastSelf]
  rw [heq]
  simpa [NumConvSpec.unsignedMax, NumConvSpec.modulus, core.num.Usize.MIN, core.num.Usize.MAX, Usize.max, Usize.numBits, UScalar.max, UScalarTy.numBits] using
    unsignedChecked_spec x core.num.Usize.MIN core.num.Usize.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [UScalarTy.numBits])

theorem saturating_truncate_i8_i8_spec (x : I8) :
  ∃ out, saturating_truncate_i8_i8 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : saturating_truncate_i8_i8 x = signedSat x core.num.I8.MIN core.num.I8.MAX := by
    simp only [saturating_truncate_i8_i8, release.Truncate.Blanket.saturating_truncate,
      I8.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.saturating_truncate,
      signedSat, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedSat_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i8_i8_spec (x : I8) :
  ∃ out, checked_truncate_i8_i8 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : checked_truncate_i8_i8 x = signedChecked x core.num.I8.MIN core.num.I8.MAX := by
    simp only [checked_truncate_i8_i8, release.Truncate.Blanket.checked_truncate,
      I8.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.checked_truncate,
      signedChecked, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedChecked_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i16_i8_spec (x : I16) :
  ∃ out, saturating_truncate_i16_i8 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : saturating_truncate_i16_i8 x = signedSat x core.num.I8.MIN core.num.I8.MAX := by
    simp only [saturating_truncate_i16_i8, release.Truncate.Blanket.saturating_truncate,
      I16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedSat_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i16_i8_spec (x : I16) :
  ∃ out, checked_truncate_i16_i8 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : checked_truncate_i16_i8 x = signedChecked x core.num.I8.MIN core.num.I8.MAX := by
    simp only [checked_truncate_i16_i8, release.Truncate.Blanket.checked_truncate,
      I16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedChecked_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i32_i8_spec (x : I32) :
  ∃ out, saturating_truncate_i32_i8 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : saturating_truncate_i32_i8 x = signedSat x core.num.I8.MIN core.num.I8.MAX := by
    simp only [saturating_truncate_i32_i8, release.Truncate.Blanket.saturating_truncate,
      I32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedSat_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i32_i8_spec (x : I32) :
  ∃ out, checked_truncate_i32_i8 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : checked_truncate_i32_i8 x = signedChecked x core.num.I8.MIN core.num.I8.MAX := by
    simp only [checked_truncate_i32_i8, release.Truncate.Blanket.checked_truncate,
      I32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedChecked_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i64_i8_spec (x : I64) :
  ∃ out, saturating_truncate_i64_i8 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : saturating_truncate_i64_i8 x = signedSat x core.num.I8.MIN core.num.I8.MAX := by
    simp only [saturating_truncate_i64_i8, release.Truncate.Blanket.saturating_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedSat_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i64_i8_spec (x : I64) :
  ∃ out, checked_truncate_i64_i8 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : checked_truncate_i64_i8 x = signedChecked x core.num.I8.MIN core.num.I8.MAX := by
    simp only [checked_truncate_i64_i8, release.Truncate.Blanket.checked_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedChecked_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i128_i8_spec (x : I128) :
  ∃ out, saturating_truncate_i128_i8 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : saturating_truncate_i128_i8 x = signedSat x core.num.I8.MIN core.num.I8.MAX := by
    simp only [saturating_truncate_i128_i8, release.Truncate.Blanket.saturating_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedSat_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i128_i8_spec (x : I128) :
  ∃ out, checked_truncate_i128_i8 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : checked_truncate_i128_i8 x = signedChecked x core.num.I8.MIN core.num.I8.MAX := by
    simp only [checked_truncate_i128_i8, release.Truncate.Blanket.checked_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedChecked_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_isize_i8_spec (x : Isize) :
  ∃ out, saturating_truncate_isize_i8 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : saturating_truncate_isize_i8 x = signedSat x core.num.I8.MIN core.num.I8.MAX := by
    simp only [saturating_truncate_isize_i8, release.Truncate.Blanket.saturating_truncate,
      Isize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedSat_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_isize_i8_spec (x : Isize) :
  ∃ out, checked_truncate_isize_i8 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 8) (NumConvSpec.signedMax 8) x.val := by
  have heq : checked_truncate_isize_i8 x = signedChecked x core.num.I8.MIN core.num.I8.MAX := by
    simp only [checked_truncate_isize_i8, release.Truncate.Blanket.checked_truncate,
      Isize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI8.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I8.MIN, core.num.I8.MAX, I8.rMin, I8.rMax] using
    signedChecked_spec x core.num.I8.MIN core.num.I8.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i16_i16_spec (x : I16) :
  ∃ out, saturating_truncate_i16_i16 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : saturating_truncate_i16_i16 x = signedSat x core.num.I16.MIN core.num.I16.MAX := by
    simp only [saturating_truncate_i16_i16, release.Truncate.Blanket.saturating_truncate,
      I16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.saturating_truncate,
      signedSat, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedSat_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i16_i16_spec (x : I16) :
  ∃ out, checked_truncate_i16_i16 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : checked_truncate_i16_i16 x = signedChecked x core.num.I16.MIN core.num.I16.MAX := by
    simp only [checked_truncate_i16_i16, release.Truncate.Blanket.checked_truncate,
      I16.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.checked_truncate,
      signedChecked, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedChecked_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i32_i16_spec (x : I32) :
  ∃ out, saturating_truncate_i32_i16 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : saturating_truncate_i32_i16 x = signedSat x core.num.I16.MIN core.num.I16.MAX := by
    simp only [saturating_truncate_i32_i16, release.Truncate.Blanket.saturating_truncate,
      I32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedSat_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i32_i16_spec (x : I32) :
  ∃ out, checked_truncate_i32_i16 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : checked_truncate_i32_i16 x = signedChecked x core.num.I16.MIN core.num.I16.MAX := by
    simp only [checked_truncate_i32_i16, release.Truncate.Blanket.checked_truncate,
      I32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedChecked_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i64_i16_spec (x : I64) :
  ∃ out, saturating_truncate_i64_i16 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : saturating_truncate_i64_i16 x = signedSat x core.num.I16.MIN core.num.I16.MAX := by
    simp only [saturating_truncate_i64_i16, release.Truncate.Blanket.saturating_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedSat_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i64_i16_spec (x : I64) :
  ∃ out, checked_truncate_i64_i16 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : checked_truncate_i64_i16 x = signedChecked x core.num.I16.MIN core.num.I16.MAX := by
    simp only [checked_truncate_i64_i16, release.Truncate.Blanket.checked_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedChecked_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i128_i16_spec (x : I128) :
  ∃ out, saturating_truncate_i128_i16 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : saturating_truncate_i128_i16 x = signedSat x core.num.I16.MIN core.num.I16.MAX := by
    simp only [saturating_truncate_i128_i16, release.Truncate.Blanket.saturating_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedSat_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i128_i16_spec (x : I128) :
  ∃ out, checked_truncate_i128_i16 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : checked_truncate_i128_i16 x = signedChecked x core.num.I16.MIN core.num.I16.MAX := by
    simp only [checked_truncate_i128_i16, release.Truncate.Blanket.checked_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedChecked_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_isize_i16_spec (x : Isize) :
  ∃ out, saturating_truncate_isize_i16 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : saturating_truncate_isize_i16 x = signedSat x core.num.I16.MIN core.num.I16.MAX := by
    simp only [saturating_truncate_isize_i16, release.Truncate.Blanket.saturating_truncate,
      Isize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedSat_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_isize_i16_spec (x : Isize) :
  ∃ out, checked_truncate_isize_i16 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 16) (NumConvSpec.signedMax 16) x.val := by
  have heq : checked_truncate_isize_i16 x = signedChecked x core.num.I16.MIN core.num.I16.MAX := by
    simp only [checked_truncate_isize_i16, release.Truncate.Blanket.checked_truncate,
      Isize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI16.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I16.MIN, core.num.I16.MAX, I16.rMin, I16.rMax] using
    signedChecked_spec x core.num.I16.MIN core.num.I16.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i32_i32_spec (x : I32) :
  ∃ out, saturating_truncate_i32_i32 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val := by
  have heq : saturating_truncate_i32_i32 x = signedSat x core.num.I32.MIN core.num.I32.MAX := by
    simp only [saturating_truncate_i32_i32, release.Truncate.Blanket.saturating_truncate,
      I32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI32.saturating_truncate,
      signedSat, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I32.MIN, core.num.I32.MAX, I32.rMin, I32.rMax] using
    signedSat_spec x core.num.I32.MIN core.num.I32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i32_i32_spec (x : I32) :
  ∃ out, checked_truncate_i32_i32 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val := by
  have heq : checked_truncate_i32_i32 x = signedChecked x core.num.I32.MIN core.num.I32.MAX := by
    simp only [checked_truncate_i32_i32, release.Truncate.Blanket.checked_truncate,
      I32.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI32.checked_truncate,
      signedChecked, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I32.MIN, core.num.I32.MAX, I32.rMin, I32.rMax] using
    signedChecked_spec x core.num.I32.MIN core.num.I32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i64_i32_spec (x : I64) :
  ∃ out, saturating_truncate_i64_i32 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val := by
  have heq : saturating_truncate_i64_i32 x = signedSat x core.num.I32.MIN core.num.I32.MAX := by
    simp only [saturating_truncate_i64_i32, release.Truncate.Blanket.saturating_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI32.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I32.MIN, core.num.I32.MAX, I32.rMin, I32.rMax] using
    signedSat_spec x core.num.I32.MIN core.num.I32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i64_i32_spec (x : I64) :
  ∃ out, checked_truncate_i64_i32 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val := by
  have heq : checked_truncate_i64_i32 x = signedChecked x core.num.I32.MIN core.num.I32.MAX := by
    simp only [checked_truncate_i64_i32, release.Truncate.Blanket.checked_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI32.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I32.MIN, core.num.I32.MAX, I32.rMin, I32.rMax] using
    signedChecked_spec x core.num.I32.MIN core.num.I32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i128_i32_spec (x : I128) :
  ∃ out, saturating_truncate_i128_i32 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val := by
  have heq : saturating_truncate_i128_i32 x = signedSat x core.num.I32.MIN core.num.I32.MAX := by
    simp only [saturating_truncate_i128_i32, release.Truncate.Blanket.saturating_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI32.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I32.MIN, core.num.I32.MAX, I32.rMin, I32.rMax] using
    signedSat_spec x core.num.I32.MIN core.num.I32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i128_i32_spec (x : I128) :
  ∃ out, checked_truncate_i128_i32 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 32) (NumConvSpec.signedMax 32) x.val := by
  have heq : checked_truncate_i128_i32 x = signedChecked x core.num.I32.MIN core.num.I32.MAX := by
    simp only [checked_truncate_i128_i32, release.Truncate.Blanket.checked_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI32.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I32.MIN, core.num.I32.MAX, I32.rMin, I32.rMax] using
    signedChecked_spec x core.num.I32.MIN core.num.I32.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i64_i64_spec (x : I64) :
  ∃ out, saturating_truncate_i64_i64 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 64) (NumConvSpec.signedMax 64) x.val := by
  have heq : saturating_truncate_i64_i64 x = signedSat x core.num.I64.MIN core.num.I64.MAX := by
    simp only [saturating_truncate_i64_i64, release.Truncate.Blanket.saturating_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI64.saturating_truncate,
      signedSat, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I64.MIN, core.num.I64.MAX, I64.rMin, I64.rMax] using
    signedSat_spec x core.num.I64.MIN core.num.I64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i64_i64_spec (x : I64) :
  ∃ out, checked_truncate_i64_i64 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 64) (NumConvSpec.signedMax 64) x.val := by
  have heq : checked_truncate_i64_i64 x = signedChecked x core.num.I64.MIN core.num.I64.MAX := by
    simp only [checked_truncate_i64_i64, release.Truncate.Blanket.checked_truncate,
      I64.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI64.checked_truncate,
      signedChecked, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I64.MIN, core.num.I64.MAX, I64.rMin, I64.rMax] using
    signedChecked_spec x core.num.I64.MIN core.num.I64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i128_i64_spec (x : I128) :
  ∃ out, saturating_truncate_i128_i64 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 64) (NumConvSpec.signedMax 64) x.val := by
  have heq : saturating_truncate_i128_i64 x = signedSat x core.num.I64.MIN core.num.I64.MAX := by
    simp only [saturating_truncate_i128_i64, release.Truncate.Blanket.saturating_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI64.saturating_truncate,
      signedSat, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I64.MIN, core.num.I64.MAX, I64.rMin, I64.rMax] using
    signedSat_spec x core.num.I64.MIN core.num.I64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i128_i64_spec (x : I128) :
  ∃ out, checked_truncate_i128_i64 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 64) (NumConvSpec.signedMax 64) x.val := by
  have heq : checked_truncate_i128_i64 x = signedChecked x core.num.I64.MIN core.num.I64.MAX := by
    simp only [checked_truncate_i128_i64, release.Truncate.Blanket.checked_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI64.checked_truncate,
      signedChecked, lift, bind_ok]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I64.MIN, core.num.I64.MAX, I64.rMin, I64.rMax] using
    signedChecked_spec x core.num.I64.MIN core.num.I64.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_i128_i128_spec (x : I128) :
  ∃ out, saturating_truncate_i128_i128 x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin 128) (NumConvSpec.signedMax 128) x.val := by
  have heq : saturating_truncate_i128_i128 x = signedSat x core.num.I128.MIN core.num.I128.MAX := by
    simp only [saturating_truncate_i128_i128, release.Truncate.Blanket.saturating_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI128.saturating_truncate,
      signedSat, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I128.MIN, core.num.I128.MAX, I128.rMin, I128.rMax] using
    signedSat_spec x core.num.I128.MIN core.num.I128.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by decide)

theorem checked_truncate_i128_i128_spec (x : I128) :
  ∃ out, checked_truncate_i128_i128 x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin 128) (NumConvSpec.signedMax 128) x.val := by
  have heq : checked_truncate_i128_i128 x = signedChecked x core.num.I128.MIN core.num.I128.MAX := by
    simp only [checked_truncate_i128_i128, release.Truncate.Blanket.checked_truncate,
      I128.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedI128.checked_truncate,
      signedChecked, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.I128.MIN, core.num.I128.MAX, I128.rMin, I128.rMax] using
    signedChecked_spec x core.num.I128.MIN core.num.I128.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

theorem saturating_truncate_isize_isize_spec (x : Isize) :
  ∃ out, saturating_truncate_isize_isize x = Result.ok out ∧ out.val = NumConvSpec.saturate (NumConvSpec.signedMin IScalarTy.Isize.numBits) (NumConvSpec.signedMax IScalarTy.Isize.numBits) x.val := by
  have heq : saturating_truncate_isize_isize x = signedSat x core.num.Isize.MIN core.num.Isize.MAX := by
    simp only [saturating_truncate_isize_isize, release.Truncate.Blanket.saturating_truncate,
      Isize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedIsize.saturating_truncate,
      signedSat, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.Isize.MIN, core.num.Isize.MAX, Isize.min, Isize.max, Isize.numBits, IScalar.min, IScalar.max, IScalarTy.numBits] using
    signedSat_spec x core.num.Isize.MIN core.num.Isize.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits]) (by scalar_tac)

theorem checked_truncate_isize_isize_spec (x : Isize) :
  ∃ out, checked_truncate_isize_isize x = Result.ok out ∧ out.map (fun v => v.val) = NumConvSpec.checked (NumConvSpec.signedMin IScalarTy.Isize.numBits) (NumConvSpec.signedMax IScalarTy.Isize.numBits) x.val := by
  have heq : checked_truncate_isize_isize x = signedChecked x core.num.Isize.MIN core.num.Isize.MAX := by
    simp only [checked_truncate_isize_isize, release.Truncate.Blanket.checked_truncate,
      Isize.Insts.Num_conv_verification_apiReleaseSealedTruncateTargetSealedIsize.checked_truncate,
      signedChecked, signedCastSelf]
  rw [heq]
  simpa [NumConvSpec.signedMin, NumConvSpec.signedMax, NumConvSpec.modulus, core.num.Isize.MIN, core.num.Isize.MAX, Isize.min, Isize.max, Isize.numBits, IScalar.min, IScalar.max, IScalarTy.numBits] using
    signedChecked_spec x core.num.Isize.MIN core.num.Isize.MAX (by rcases System.Platform.numBits_eq with h | h <;> simp_all [IScalarTy.numBits])

end NumConvProof
