import Proofs.Recognition
set_option maxRecDepth 16384

open Aeneas Aeneas.Std Result

namespace LexicalParseIntegerProofs

private def swar4 (v : Std.U32) : Bool :=
  decide (((v.bv + 1179010630#32 ||| v.bv - 808464432#32)
    &&& 2155905152#32) = 0#32)

theorem is4_eq_swar (v : Std.U32) :
    lexical_parse_integer_swar_harness.is_4digits v = .ok (swar4 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 10#u32 : Result Std.U32) = .ok 70#u32 := by rfl
  have h2 : (70#u32 <<< 8#i32 : Result Std.U32) = .ok 17920#u32 := by rfl
  have h3 : (70#u32 + 17920#u32 : Result Std.U32) = .ok 17990#u32 := by rfl
  have h4 : (70#u32 <<< 16#i32 : Result Std.U32) = .ok 4587520#u32 := by rfl
  have h5 : (17990#u32 + 4587520#u32 : Result Std.U32) = .ok 4605510#u32 := by rfl
  have h6 : (70#u32 <<< 24#i32 : Result Std.U32) = .ok 1174405120#u32 := by rfl
  have h7 : (4605510#u32 + 1174405120#u32 : Result Std.U32) = .ok 1179010630#u32 := by rfl
  simp [swar4, lexical_parse_integer_swar_harness.is_4digits,
    h0, h1, h2, h3, h4, h5, h6, h7,
    core.num.U32.wrapping_add, core.num.U32.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is4_total (v : Std.U32) :
    ∃ out : Bool, lexical_parse_integer_swar_harness.is_4digits v = .ok out := by
  exact ⟨swar4 v, is4_eq_swar v⟩

private def swar8 (v : Std.U64) : Bool :=
  decide (((v.bv + 5063812098665367110#64 ||| v.bv - 3472328296227680304#64)
    &&& 9259542123273814144#64) = 0#64)

theorem is8_eq_swar (v : Std.U64) :
    lexical_parse_integer_swar_harness.is_8digits v = .ok (swar8 v) := by
  have h0 : (70#u32 + 10#u32 : Result Std.U32) = .ok 80#u32 := by rfl
  have h1 : (80#u32 - 10#u32 : Result Std.U32) = .ok 70#u32 := by rfl
  have h2 : (70#u32 <<< 8#i32 : Result Std.U32) = .ok 17920#u32 := by rfl
  have h3 : (70#u32 + 17920#u32 : Result Std.U32) = .ok 17990#u32 := by rfl
  have h4 : (70#u32 <<< 16#i32 : Result Std.U32) = .ok 4587520#u32 := by rfl
  have h5 : (17990#u32 + 4587520#u32 : Result Std.U32) = .ok 4605510#u32 := by rfl
  have h6 : (70#u32 <<< 24#i32 : Result Std.U32) = .ok 1174405120#u32 := by rfl
  have h7 : (4605510#u32 + 1174405120#u32 : Result Std.U32) = .ok 1179010630#u32 := by rfl
  have hc : UScalar.cast .U64 1179010630#u32 = (1179010630#u64 : Std.U64) := by rfl
  have h8 : (1179010630#u64 <<< 32#i32 : Result Std.U64) =
      .ok 5063812097486356480#u64 := by rfl
  simp [swar8, lexical_parse_integer_swar_harness.is_8digits,
    h0, h1, h2, h3, h4, h5, h6, h7, hc, h8,
    core.num.U64.wrapping_add, core.num.U64.wrapping_sub,
    UScalar.wrapping_add, UScalar.wrapping_sub, Std.lift]
  simp only [UScalar.eq_equiv_bv_eq]
  rfl

theorem is8_total (v : Std.U64) :
    ∃ out : Bool, lexical_parse_integer_swar_harness.is_8digits v = .ok out := by
  exact ⟨swar8 v, is8_eq_swar v⟩

theorem bitvec_mask_nat {w : Nat} (v a b m : BitVec w) :
 (((v+a ||| v-b)&&&m)=0#w) ↔
 (((v.toNat+a.toNat)%2^w ||| ((2^w-b.toNat)+v.toNat)%2^w)&&&m.toNat=0) := by
 rw [←BitVec.toNat_inj]
 simp only [BitVec.toNat_and,BitVec.toNat_or,BitVec.toNat_add,BitVec.toNat_sub,
   BitVec.toNat_ofNat, Nat.zero_mod]

theorem swar4_correct (v : Std.U32) :
 swar4 v = true ↔ LexicalParseIntegerSpec.decimal4Digits v.val := by
 have h := recognition_mask 4 v.val
 have hc0 : repeated 70 4 = 1179010630 := by norm_num [repeated]
 have hc1 : repeated 48 4 = 808464432 := by norm_num [repeated]
 have hc2 : repeated 128 4 = 2155905152 := by norm_num [repeated]
 have hp : 256^4 = 4294967296 := by norm_num
 simp only [hc0,hc1,hc2,hp] at h
 have hsub : v.val+4294967296-808464432=v.val+3486502864 := by omega
 rw [hsub] at h
 simp only [swar4,decide_eq_true_eq,bitvec_mask_nat,BitVec.toNat_ofNat]
 norm_num only
 rw [UScalar.bv_toNat]
 conv_lhs => lhs; lhs; rhs; lhs; rw [Nat.add_comm]
 unfold LexicalParseIntegerSpec.decimal4Digits
 exact h

theorem swar8_correct (v : Std.U64) :
 swar8 v = true ↔ LexicalParseIntegerSpec.decimal8Digits v.val := by
 have h := recognition_mask 8 v.val
 have hc0 : repeated 70 8 = 5063812098665367110 := by norm_num [repeated]
 have hc1 : repeated 48 8 = 3472328296227680304 := by norm_num [repeated]
 have hc2 : repeated 128 8 = 9259542123273814144 := by norm_num [repeated]
 have hp : 256^8 = 18446744073709551616 := by norm_num
 simp only [hc0,hc1,hc2,hp] at h
 have hsub : v.val+18446744073709551616-3472328296227680304=v.val+14974415777481871312 := by omega
 rw [hsub] at h
 simp only [swar8,decide_eq_true_eq,bitvec_mask_nat,BitVec.toNat_ofNat]
 norm_num only
 rw [UScalar.bv_toNat]
 conv_lhs => lhs; lhs; rhs; lhs; rw [Nat.add_comm]
 unfold LexicalParseIntegerSpec.decimal8Digits
 exact h

theorem is4_decimal (v : Std.U32) :
 ∃ out, lexical_parse_integer_swar_harness.is_4digits v = .ok out ∧
   (out = true ↔ LexicalParseIntegerSpec.decimal4Digits v.val) :=
 ⟨swar4 v,is4_eq_swar v,swar4_correct v⟩

theorem is8_decimal (v : Std.U64) :
 ∃ out, lexical_parse_integer_swar_harness.is_8digits v = .ok out ∧
   (out = true ↔ LexicalParseIntegerSpec.decimal8Digits v.val) :=
 ⟨swar8 v,is8_eq_swar v,swar8_correct v⟩

end LexicalParseIntegerProofs