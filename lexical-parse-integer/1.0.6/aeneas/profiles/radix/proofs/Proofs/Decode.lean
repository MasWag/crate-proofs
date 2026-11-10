import Proofs.Validate

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result
namespace LexicalParseIntegerRadixProofs

theorem parse4_arithmetic_radix2 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 2#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*2 + (v.val-808464432)/256)%128)*2*2 +
        (((v.val - 808464432)*2 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix3 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 3#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*3 + (v.val-808464432)/256)%128)*3*3 +
        (((v.val - 808464432)*3 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix4 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 4#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*4 + (v.val-808464432)/256)%128)*4*4 +
        (((v.val - 808464432)*4 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix5 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 5#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*5 + (v.val-808464432)/256)%128)*5*5 +
        (((v.val - 808464432)*5 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix6 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 6#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*6 + (v.val-808464432)/256)%128)*6*6 +
        (((v.val - 808464432)*6 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix7 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 7#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*7 + (v.val-808464432)/256)%128)*7*7 +
        (((v.val - 808464432)*7 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix8 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 8#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*8 + (v.val-808464432)/256)%128)*8*8 +
        (((v.val - 808464432)*8 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix9 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 9#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*9 + (v.val-808464432)/256)%128)*9*9 +
        (((v.val - 808464432)*9 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic_radix10 (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits 10#u32 v
      ⦃ out => out.val =
        (((v.val - 808464432)*10 + (v.val-808464432)/256)%128)*10*10 +
        (((v.val - 808464432)*10 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_4digits
  step*
  all_goals
    have hi2 : i2.val ≤ 127 := by
      rw [i2_post, UScalar.val_and]
      exact Nat.and_le_right
  all_goals try (simp only [U32.max_eq]; scalar_tac)
  · have hi6 : i6.val ≤ 127 := by
      rw [i6_post, UScalar.val_and]
      exact Nat.and_le_right
    simp only [U32.max_eq]
    scalar_tac
  · simp only [out_post, i4_post, i3_post, i2_post, i6_post,
      UScalar.val_and, i5_post, v2_post, i_post, i1_post, v1_post,
      Nat.shiftRight_eq_div_pow, UScalar.ofNatCore_val_eq]
    norm_num only at *
    simp only [show (127 : Nat) = 2^7-1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

theorem parse4_arithmetic (r : U32) (v : U32)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_radix_harness.parse_4digits r v
      ⦃ out => out.val =
        (((v.val - 808464432)*r.val + (v.val-808464432)/256)%128)*r.val*r.val +
        (((v.val - 808464432)*r.val + (v.val-808464432)/256)/65536)%128 ⦄ := by
  have hcases : r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 
  · have heq : r = 2#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h2)
    rw [heq]
    simpa using parse4_arithmetic_radix2 v hl hu
  · have heq : r = 3#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h3)
    rw [heq]
    simpa using parse4_arithmetic_radix3 v hl hu
  · have heq : r = 4#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h4)
    rw [heq]
    simpa using parse4_arithmetic_radix4 v hl hu
  · have heq : r = 5#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h5)
    rw [heq]
    simpa using parse4_arithmetic_radix5 v hl hu
  · have heq : r = 6#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h6)
    rw [heq]
    simpa using parse4_arithmetic_radix6 v hl hu
  · have heq : r = 7#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h7)
    rw [heq]
    simpa using parse4_arithmetic_radix7 v hl hu
  · have heq : r = 8#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h8)
    rw [heq]
    simpa using parse4_arithmetic_radix8 v hl hu
  · have heq : r = 9#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h9)
    rw [heq]
    simpa using parse4_arithmetic_radix9 v hl hu
  · have heq : r = 10#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h10)
    rw [heq]
    simpa using parse4_arithmetic_radix10 v hl hu

theorem parse8_arithmetic_radix2 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 2#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*2 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (4+64*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*2 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+16*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix3 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 3#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*3 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (9+729*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*3 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+81*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix4 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 4#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*4 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (16+4096*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*4 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+256*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix5 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 5#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*5 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (25+15625*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*5 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+625*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix6 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 6#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*6 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (36+46656*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*6 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+1296*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix7 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 7#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*7 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (49+117649*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*7 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+2401*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix8 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 8#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*8 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (64+262144*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*8 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+4096*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix9 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 9#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*9 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (81+531441*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*9 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+6561*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic_radix10 (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits 10#u32 v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*10 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (100+1000000*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*10 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+10000*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_radix_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix1_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

theorem parse8_arithmetic (r : U32) (v : U64)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_radix_harness.parse_8digits r v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*r.val + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (r.val^2+r.val^6*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*r.val + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+r.val^4*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  have hcases : r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 
  · have heq : r = 2#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h2)
    rw [heq]
    simpa using parse8_arithmetic_radix2 v hl hu
  · have heq : r = 3#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h3)
    rw [heq]
    simpa using parse8_arithmetic_radix3 v hl hu
  · have heq : r = 4#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h4)
    rw [heq]
    simpa using parse8_arithmetic_radix4 v hl hu
  · have heq : r = 5#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h5)
    rw [heq]
    simpa using parse8_arithmetic_radix5 v hl hu
  · have heq : r = 6#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h6)
    rw [heq]
    simpa using parse8_arithmetic_radix6 v hl hu
  · have heq : r = 7#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h7)
    rw [heq]
    simpa using parse8_arithmetic_radix7 v hl hu
  · have heq : r = 8#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h8)
    rw [heq]
    simpa using parse8_arithmetic_radix8 v hl hu
  · have heq : r = 9#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h9)
    rw [heq]
    simpa using parse8_arithmetic_radix9 v hl hu
  · have heq : r = 10#u32 := by
      cases r with
      | mk bv =>
        congr
        exact BitVec.toNat_inj.mp (by simpa [UScalar.val] using h10)
    rw [heq]
    simpa using parse8_arithmetic_radix10 v hl hu

private theorem packed4_radix2 (a b c d : Nat)
    (ha : a < 2) (hb : b < 2) (hc : c < 2) (hd : d < 2) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*2 + n/256
    (q%128)*2*2 + (q/65536)%128 = 8*a + 4*b + 2*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*2 +
      (b + 256*c + 65536*d))%128 = 2*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*2 +
      (b + 256*c + 65536*d))/65536 = 2*c + d + 512*d := by omega
  rw [hhi]
  have hh : (2*c + d + 512*d)%128 = 2*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix3 (a b c d : Nat)
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*3 + n/256
    (q%128)*3*3 + (q/65536)%128 = 27*a + 9*b + 3*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*3 +
      (b + 256*c + 65536*d))%128 = 3*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*3 +
      (b + 256*c + 65536*d))/65536 = 3*c + d + 768*d := by omega
  rw [hhi]
  have hh : (3*c + d + 768*d)%128 = 3*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix4 (a b c d : Nat)
    (ha : a < 4) (hb : b < 4) (hc : c < 4) (hd : d < 4) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*4 + n/256
    (q%128)*4*4 + (q/65536)%128 = 64*a + 16*b + 4*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*4 +
      (b + 256*c + 65536*d))%128 = 4*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*4 +
      (b + 256*c + 65536*d))/65536 = 4*c + d + 1024*d := by omega
  rw [hhi]
  have hh : (4*c + d + 1024*d)%128 = 4*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix5 (a b c d : Nat)
    (ha : a < 5) (hb : b < 5) (hc : c < 5) (hd : d < 5) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*5 + n/256
    (q%128)*5*5 + (q/65536)%128 = 125*a + 25*b + 5*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*5 +
      (b + 256*c + 65536*d))%128 = 5*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*5 +
      (b + 256*c + 65536*d))/65536 = 5*c + d + 1280*d := by omega
  rw [hhi]
  have hh : (5*c + d + 1280*d)%128 = 5*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix6 (a b c d : Nat)
    (ha : a < 6) (hb : b < 6) (hc : c < 6) (hd : d < 6) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*6 + n/256
    (q%128)*6*6 + (q/65536)%128 = 216*a + 36*b + 6*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*6 +
      (b + 256*c + 65536*d))%128 = 6*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*6 +
      (b + 256*c + 65536*d))/65536 = 6*c + d + 1536*d := by omega
  rw [hhi]
  have hh : (6*c + d + 1536*d)%128 = 6*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix7 (a b c d : Nat)
    (ha : a < 7) (hb : b < 7) (hc : c < 7) (hd : d < 7) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*7 + n/256
    (q%128)*7*7 + (q/65536)%128 = 343*a + 49*b + 7*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*7 +
      (b + 256*c + 65536*d))%128 = 7*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*7 +
      (b + 256*c + 65536*d))/65536 = 7*c + d + 1792*d := by omega
  rw [hhi]
  have hh : (7*c + d + 1792*d)%128 = 7*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix8 (a b c d : Nat)
    (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*8 + n/256
    (q%128)*8*8 + (q/65536)%128 = 512*a + 64*b + 8*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*8 +
      (b + 256*c + 65536*d))%128 = 8*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*8 +
      (b + 256*c + 65536*d))/65536 = 8*c + d + 2048*d := by omega
  rw [hhi]
  have hh : (8*c + d + 2048*d)%128 = 8*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix9 (a b c d : Nat)
    (ha : a < 9) (hb : b < 9) (hc : c < 9) (hd : d < 9) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*9 + n/256
    (q%128)*9*9 + (q/65536)%128 = 729*a + 81*b + 9*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*9 +
      (b + 256*c + 65536*d))%128 = 9*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*9 +
      (b + 256*c + 65536*d))/65536 = 9*c + d + 2304*d := by omega
  rw [hhi]
  have hh : (9*c + d + 2304*d)%128 = 9*c + d := by omega
  rw [hh]
  omega

private theorem packed4_radix10 (a b c d : Nat)
    (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*10 + n/256
    (q%128)*10*10 + (q/65536)%128 = 1000*a + 100*b + 10*c + d := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d)/256 =
      b + 256*c + 65536*d := by omega
  rw [hq]
  have hlo : ((a + 256*b + 65536*c + 16777216*d)*10 +
      (b + 256*c + 65536*d))%128 = 10*a + b := by omega
  rw [hlo]
  have hhi : ((a + 256*b + 65536*c + 16777216*d)*10 +
      (b + 256*c + 65536*d))/65536 = 10*c + d + 2560*d := by omega
  rw [hhi]
  have hh : (10*c + d + 2560*d)%128 = 10*c + d := by omega
  rw [hh]
  omega

theorem packed4_arithmetic (r a b c d : Nat)
    (hr : 2 ≤ r ∧ r ≤ 10)
    (ha : a < r) (hb : b < r) (hc : c < r) (hd : d < r) :
    let n := a + 256*b + 65536*c + 16777216*d
    let q := n*r + n/256
    (q%128)*r*r + (q/65536)%128 = r^3*a + r^2*b + r*c + d := by
  have hcases : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 
  · subst r
    simpa using packed4_radix2 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix3 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix4 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix5 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix6 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix7 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix8 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix9 a b c d ha hb hc hd
  · subst r
    simpa using packed4_radix10 a b c d ha hb hc hd

theorem parse4_packed (r : U32) (v : U32) (a b c d : Nat)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (ha : a < r.val) (hb : b < r.val) (hc : c < r.val) (hd : d < r.val)
    (hv : v.val = 808464432 + a + 256*b + 65536*c + 16777216*d) :
    lexical_parse_integer_radix_harness.parse_4digits r v
      ⦃ out => out.val = r.val^3*a + r.val^2*b + r.val*c + d ⦄ := by
  have hl : 808464432 ≤ v.val := by omega
  have hu : v.val ≤ 960051513 := by omega
  have hn : v.val - 808464432 = a + 256*b + 65536*c + 16777216*d := by omega
  have he := packed4_arithmetic r.val a b c d hr ha hb hc hd
  have h := parse4_arithmetic r v hr hl hu
  simpa only [hn, he] using h

theorem parse4_value (r : U32) (v : U32)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (hv : LexicalParseIntegerRadixSpec.digits4 r.val v.val) :
    lexical_parse_integer_radix_harness.parse_4digits r v
      ⦃ out => out.val = LexicalParseIntegerRadixSpec.value4 r.val v.val ⦄ := by
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [LexicalParseIntegerRadixSpec.asciiDigit, LexicalParseIntegerRadixSpec.byteAt] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have hbound : v.val ≤ 4294967295 := by scalar_tac
  have hp : v.val = 808464432 + (v.val % 256-48) + 256*(v.val/256%256-48) +
      65536*(v.val/65536%256-48) + 16777216*(v.val/16777216%256-48) := by omega
  have h := parse4_packed r v _ _ _ _ hr (by omega) (by omega) (by omega) (by omega) hp
  simpa [LexicalParseIntegerRadixSpec.value4, LexicalParseIntegerRadixSpec.wordValue,
    LexicalParseIntegerRadixSpec.textValue, LexicalParseIntegerRadixSpec.byteAt,
    List.range_succ, pow_succ, pow_zero, Nat.mul_add, Nat.add_mul, ←Nat.mul_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun value _ hp => ⟨value, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem parse4_value_success (r : U32) (v : U32)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (hv : LexicalParseIntegerRadixSpec.digits4 r.val v.val) :
    ∃ out, lexical_parse_integer_radix_harness.parse_4digits r v = Result.ok out ∧
      out.val = LexicalParseIntegerRadixSpec.value4 r.val v.val :=
  result_spec_success (parse4_value r v hr hv)

theorem mask8_lanes (n : Nat) :
    n &&& 1095216660735 = n%256 + 4294967296*((n/4294967296)%256) := by
  have hlo : (n &&& 1095216660735)%4294967296 = n%256 := by
    change (n &&& 1095216660735) % (2^32) = n % (2^8)
    rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.and_two_pow_sub_one_eq_mod,
      Nat.and_assoc]
    congr 1
  have hhi : (n &&& 1095216660735)/4294967296 = (n/4294967296)%256 := by
    change (n &&& 1095216660735)/(2^32) = (n/(2^32))%(2^8)
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_and_distrib,
      ← Nat.shiftRight_eq_div_pow, ← Nat.and_two_pow_sub_one_eq_mod]
    congr 1
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix2 (a b c d e f g h : Nat)
    (ha : a<2) (hb : b<2) (hc : c<2) (hd : d<2)
    (he : e<2) (hf : f<2) (hg : g<2) (hh : h<2) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*2+n/256
    ((((p &&& 1095216660735)*(4+64*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+16*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 128*a + 64*b + 32*c + 16*d + 8*e + 4*f + 2*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 2*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (2*a+b) + 256*(1*(2*b+c) + 256*(2*c+d) + 65536*(2*d+e) + 16777216*(2*e+f) + 4294967296*(2*f+g) + 1099511627776*(2*g+h) + 281474976710656*(2*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 2*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(2*a+b) + 256*(2*b+c) + 65536*(2*c+d) + 16777216*(2*d+e)) + 4294967296*(1*(2*e+f) + 256*(2*f+g) + 65536*(2*g+h) + 16777216*(2*h)) := by ring
    have hlo : (1*(2*a+b) + 256*(2*b+c) + 65536*(2*c+d) + 16777216*(2*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(2*e+f) + 256*(2*f+g) + 65536*(2*g+h) + 16777216*(2*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(2*e+f) + 256*(2*f+g) + 65536*(2*g+h) + 16777216*(2*h)) = (2*e+f) + 256*(1*(2*f+g) + 256*(2*g+h) + 65536*(2*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 2*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(2*a+b) + 256*(2*b+c)) + 65536*(1*(2*c+d) + 256*(2*d+e) + 65536*(2*e+f) + 16777216*(2*f+g) + 4294967296*(2*g+h) + 1099511627776*(2*h)) := by ring
    have hlo : (1*(2*a+b) + 256*(2*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(2*c+d) + 256*(2*d+e) + 65536*(2*e+f) + 16777216*(2*f+g) + 4294967296*(2*g+h) + 1099511627776*(2*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(2*c+d) + 256*(2*d+e) + 65536*(2*e+f) + 16777216*(2*f+g) + 4294967296*(2*g+h) + 1099511627776*(2*h)) = (2*c+d) + 256*(1*(2*d+e) + 256*(2*e+f) + 65536*(2*f+g) + 16777216*(2*g+h) + 4294967296*(2*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 2*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(2*a+b) + 256*(2*b+c) + 65536*(2*c+d) + 16777216*(2*d+e) + 4294967296*(2*e+f) + 1099511627776*(2*f+g)) + 281474976710656*(1*(2*g+h) + 256*(2*h)) := by ring
    have hlo : (1*(2*a+b) + 256*(2*b+c) + 65536*(2*c+d) + 16777216*(2*d+e) + 4294967296*(2*e+f) + 1099511627776*(2*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*2+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(2*g+h) + 256*(2*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(2*g+h) + 256*(2*h)) = (2*g+h) + 256*(1*(2*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (2*a+b+4294967296*(2*e+f))*(4+64*4294967296) +
      (2*c+d+4294967296*(2*g+h))*(1+16*4294967296) =
      (4*(2*a+b)+(2*c+d)) +
      4294967296*(64*(2*a+b)+16*(2*c+d)+4*(2*e+f)+(2*g+h)) +
      18446744073709551616*(64*(2*e+f)+16*(2*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (4*(2*a+b)+(2*c+d)) +
      4294967296*(64*(2*a+b)+16*(2*c+d)+4*(2*e+f)+(2*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 4*(2*a+b)+(2*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 64*(2*a+b)+16*(2*c+d)+4*(2*e+f)+(2*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix3 (a b c d e f g h : Nat)
    (ha : a<3) (hb : b<3) (hc : c<3) (hd : d<3)
    (he : e<3) (hf : f<3) (hg : g<3) (hh : h<3) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*3+n/256
    ((((p &&& 1095216660735)*(9+729*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+81*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 2187*a + 729*b + 243*c + 81*d + 27*e + 9*f + 3*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 3*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (3*a+b) + 256*(1*(3*b+c) + 256*(3*c+d) + 65536*(3*d+e) + 16777216*(3*e+f) + 4294967296*(3*f+g) + 1099511627776*(3*g+h) + 281474976710656*(3*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 3*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(3*a+b) + 256*(3*b+c) + 65536*(3*c+d) + 16777216*(3*d+e)) + 4294967296*(1*(3*e+f) + 256*(3*f+g) + 65536*(3*g+h) + 16777216*(3*h)) := by ring
    have hlo : (1*(3*a+b) + 256*(3*b+c) + 65536*(3*c+d) + 16777216*(3*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(3*e+f) + 256*(3*f+g) + 65536*(3*g+h) + 16777216*(3*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(3*e+f) + 256*(3*f+g) + 65536*(3*g+h) + 16777216*(3*h)) = (3*e+f) + 256*(1*(3*f+g) + 256*(3*g+h) + 65536*(3*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 3*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(3*a+b) + 256*(3*b+c)) + 65536*(1*(3*c+d) + 256*(3*d+e) + 65536*(3*e+f) + 16777216*(3*f+g) + 4294967296*(3*g+h) + 1099511627776*(3*h)) := by ring
    have hlo : (1*(3*a+b) + 256*(3*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(3*c+d) + 256*(3*d+e) + 65536*(3*e+f) + 16777216*(3*f+g) + 4294967296*(3*g+h) + 1099511627776*(3*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(3*c+d) + 256*(3*d+e) + 65536*(3*e+f) + 16777216*(3*f+g) + 4294967296*(3*g+h) + 1099511627776*(3*h)) = (3*c+d) + 256*(1*(3*d+e) + 256*(3*e+f) + 65536*(3*f+g) + 16777216*(3*g+h) + 4294967296*(3*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 3*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(3*a+b) + 256*(3*b+c) + 65536*(3*c+d) + 16777216*(3*d+e) + 4294967296*(3*e+f) + 1099511627776*(3*f+g)) + 281474976710656*(1*(3*g+h) + 256*(3*h)) := by ring
    have hlo : (1*(3*a+b) + 256*(3*b+c) + 65536*(3*c+d) + 16777216*(3*d+e) + 4294967296*(3*e+f) + 1099511627776*(3*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*3+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(3*g+h) + 256*(3*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(3*g+h) + 256*(3*h)) = (3*g+h) + 256*(1*(3*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (3*a+b+4294967296*(3*e+f))*(9+729*4294967296) +
      (3*c+d+4294967296*(3*g+h))*(1+81*4294967296) =
      (9*(3*a+b)+(3*c+d)) +
      4294967296*(729*(3*a+b)+81*(3*c+d)+9*(3*e+f)+(3*g+h)) +
      18446744073709551616*(729*(3*e+f)+81*(3*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (9*(3*a+b)+(3*c+d)) +
      4294967296*(729*(3*a+b)+81*(3*c+d)+9*(3*e+f)+(3*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 9*(3*a+b)+(3*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 729*(3*a+b)+81*(3*c+d)+9*(3*e+f)+(3*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix4 (a b c d e f g h : Nat)
    (ha : a<4) (hb : b<4) (hc : c<4) (hd : d<4)
    (he : e<4) (hf : f<4) (hg : g<4) (hh : h<4) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*4+n/256
    ((((p &&& 1095216660735)*(16+4096*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+256*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 16384*a + 4096*b + 1024*c + 256*d + 64*e + 16*f + 4*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 4*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (4*a+b) + 256*(1*(4*b+c) + 256*(4*c+d) + 65536*(4*d+e) + 16777216*(4*e+f) + 4294967296*(4*f+g) + 1099511627776*(4*g+h) + 281474976710656*(4*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 4*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(4*a+b) + 256*(4*b+c) + 65536*(4*c+d) + 16777216*(4*d+e)) + 4294967296*(1*(4*e+f) + 256*(4*f+g) + 65536*(4*g+h) + 16777216*(4*h)) := by ring
    have hlo : (1*(4*a+b) + 256*(4*b+c) + 65536*(4*c+d) + 16777216*(4*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(4*e+f) + 256*(4*f+g) + 65536*(4*g+h) + 16777216*(4*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(4*e+f) + 256*(4*f+g) + 65536*(4*g+h) + 16777216*(4*h)) = (4*e+f) + 256*(1*(4*f+g) + 256*(4*g+h) + 65536*(4*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 4*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(4*a+b) + 256*(4*b+c)) + 65536*(1*(4*c+d) + 256*(4*d+e) + 65536*(4*e+f) + 16777216*(4*f+g) + 4294967296*(4*g+h) + 1099511627776*(4*h)) := by ring
    have hlo : (1*(4*a+b) + 256*(4*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(4*c+d) + 256*(4*d+e) + 65536*(4*e+f) + 16777216*(4*f+g) + 4294967296*(4*g+h) + 1099511627776*(4*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(4*c+d) + 256*(4*d+e) + 65536*(4*e+f) + 16777216*(4*f+g) + 4294967296*(4*g+h) + 1099511627776*(4*h)) = (4*c+d) + 256*(1*(4*d+e) + 256*(4*e+f) + 65536*(4*f+g) + 16777216*(4*g+h) + 4294967296*(4*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 4*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(4*a+b) + 256*(4*b+c) + 65536*(4*c+d) + 16777216*(4*d+e) + 4294967296*(4*e+f) + 1099511627776*(4*f+g)) + 281474976710656*(1*(4*g+h) + 256*(4*h)) := by ring
    have hlo : (1*(4*a+b) + 256*(4*b+c) + 65536*(4*c+d) + 16777216*(4*d+e) + 4294967296*(4*e+f) + 1099511627776*(4*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*4+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(4*g+h) + 256*(4*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(4*g+h) + 256*(4*h)) = (4*g+h) + 256*(1*(4*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (4*a+b+4294967296*(4*e+f))*(16+4096*4294967296) +
      (4*c+d+4294967296*(4*g+h))*(1+256*4294967296) =
      (16*(4*a+b)+(4*c+d)) +
      4294967296*(4096*(4*a+b)+256*(4*c+d)+16*(4*e+f)+(4*g+h)) +
      18446744073709551616*(4096*(4*e+f)+256*(4*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (16*(4*a+b)+(4*c+d)) +
      4294967296*(4096*(4*a+b)+256*(4*c+d)+16*(4*e+f)+(4*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 16*(4*a+b)+(4*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 4096*(4*a+b)+256*(4*c+d)+16*(4*e+f)+(4*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix5 (a b c d e f g h : Nat)
    (ha : a<5) (hb : b<5) (hc : c<5) (hd : d<5)
    (he : e<5) (hf : f<5) (hg : g<5) (hh : h<5) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*5+n/256
    ((((p &&& 1095216660735)*(25+15625*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+625*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 78125*a + 15625*b + 3125*c + 625*d + 125*e + 25*f + 5*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 5*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (5*a+b) + 256*(1*(5*b+c) + 256*(5*c+d) + 65536*(5*d+e) + 16777216*(5*e+f) + 4294967296*(5*f+g) + 1099511627776*(5*g+h) + 281474976710656*(5*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 5*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(5*a+b) + 256*(5*b+c) + 65536*(5*c+d) + 16777216*(5*d+e)) + 4294967296*(1*(5*e+f) + 256*(5*f+g) + 65536*(5*g+h) + 16777216*(5*h)) := by ring
    have hlo : (1*(5*a+b) + 256*(5*b+c) + 65536*(5*c+d) + 16777216*(5*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(5*e+f) + 256*(5*f+g) + 65536*(5*g+h) + 16777216*(5*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(5*e+f) + 256*(5*f+g) + 65536*(5*g+h) + 16777216*(5*h)) = (5*e+f) + 256*(1*(5*f+g) + 256*(5*g+h) + 65536*(5*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 5*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(5*a+b) + 256*(5*b+c)) + 65536*(1*(5*c+d) + 256*(5*d+e) + 65536*(5*e+f) + 16777216*(5*f+g) + 4294967296*(5*g+h) + 1099511627776*(5*h)) := by ring
    have hlo : (1*(5*a+b) + 256*(5*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(5*c+d) + 256*(5*d+e) + 65536*(5*e+f) + 16777216*(5*f+g) + 4294967296*(5*g+h) + 1099511627776*(5*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(5*c+d) + 256*(5*d+e) + 65536*(5*e+f) + 16777216*(5*f+g) + 4294967296*(5*g+h) + 1099511627776*(5*h)) = (5*c+d) + 256*(1*(5*d+e) + 256*(5*e+f) + 65536*(5*f+g) + 16777216*(5*g+h) + 4294967296*(5*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 5*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(5*a+b) + 256*(5*b+c) + 65536*(5*c+d) + 16777216*(5*d+e) + 4294967296*(5*e+f) + 1099511627776*(5*f+g)) + 281474976710656*(1*(5*g+h) + 256*(5*h)) := by ring
    have hlo : (1*(5*a+b) + 256*(5*b+c) + 65536*(5*c+d) + 16777216*(5*d+e) + 4294967296*(5*e+f) + 1099511627776*(5*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*5+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(5*g+h) + 256*(5*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(5*g+h) + 256*(5*h)) = (5*g+h) + 256*(1*(5*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (5*a+b+4294967296*(5*e+f))*(25+15625*4294967296) +
      (5*c+d+4294967296*(5*g+h))*(1+625*4294967296) =
      (25*(5*a+b)+(5*c+d)) +
      4294967296*(15625*(5*a+b)+625*(5*c+d)+25*(5*e+f)+(5*g+h)) +
      18446744073709551616*(15625*(5*e+f)+625*(5*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (25*(5*a+b)+(5*c+d)) +
      4294967296*(15625*(5*a+b)+625*(5*c+d)+25*(5*e+f)+(5*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 25*(5*a+b)+(5*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 15625*(5*a+b)+625*(5*c+d)+25*(5*e+f)+(5*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix6 (a b c d e f g h : Nat)
    (ha : a<6) (hb : b<6) (hc : c<6) (hd : d<6)
    (he : e<6) (hf : f<6) (hg : g<6) (hh : h<6) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*6+n/256
    ((((p &&& 1095216660735)*(36+46656*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+1296*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 279936*a + 46656*b + 7776*c + 1296*d + 216*e + 36*f + 6*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 6*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (6*a+b) + 256*(1*(6*b+c) + 256*(6*c+d) + 65536*(6*d+e) + 16777216*(6*e+f) + 4294967296*(6*f+g) + 1099511627776*(6*g+h) + 281474976710656*(6*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 6*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(6*a+b) + 256*(6*b+c) + 65536*(6*c+d) + 16777216*(6*d+e)) + 4294967296*(1*(6*e+f) + 256*(6*f+g) + 65536*(6*g+h) + 16777216*(6*h)) := by ring
    have hlo : (1*(6*a+b) + 256*(6*b+c) + 65536*(6*c+d) + 16777216*(6*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(6*e+f) + 256*(6*f+g) + 65536*(6*g+h) + 16777216*(6*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(6*e+f) + 256*(6*f+g) + 65536*(6*g+h) + 16777216*(6*h)) = (6*e+f) + 256*(1*(6*f+g) + 256*(6*g+h) + 65536*(6*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 6*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(6*a+b) + 256*(6*b+c)) + 65536*(1*(6*c+d) + 256*(6*d+e) + 65536*(6*e+f) + 16777216*(6*f+g) + 4294967296*(6*g+h) + 1099511627776*(6*h)) := by ring
    have hlo : (1*(6*a+b) + 256*(6*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(6*c+d) + 256*(6*d+e) + 65536*(6*e+f) + 16777216*(6*f+g) + 4294967296*(6*g+h) + 1099511627776*(6*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(6*c+d) + 256*(6*d+e) + 65536*(6*e+f) + 16777216*(6*f+g) + 4294967296*(6*g+h) + 1099511627776*(6*h)) = (6*c+d) + 256*(1*(6*d+e) + 256*(6*e+f) + 65536*(6*f+g) + 16777216*(6*g+h) + 4294967296*(6*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 6*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(6*a+b) + 256*(6*b+c) + 65536*(6*c+d) + 16777216*(6*d+e) + 4294967296*(6*e+f) + 1099511627776*(6*f+g)) + 281474976710656*(1*(6*g+h) + 256*(6*h)) := by ring
    have hlo : (1*(6*a+b) + 256*(6*b+c) + 65536*(6*c+d) + 16777216*(6*d+e) + 4294967296*(6*e+f) + 1099511627776*(6*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*6+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(6*g+h) + 256*(6*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(6*g+h) + 256*(6*h)) = (6*g+h) + 256*(1*(6*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (6*a+b+4294967296*(6*e+f))*(36+46656*4294967296) +
      (6*c+d+4294967296*(6*g+h))*(1+1296*4294967296) =
      (36*(6*a+b)+(6*c+d)) +
      4294967296*(46656*(6*a+b)+1296*(6*c+d)+36*(6*e+f)+(6*g+h)) +
      18446744073709551616*(46656*(6*e+f)+1296*(6*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (36*(6*a+b)+(6*c+d)) +
      4294967296*(46656*(6*a+b)+1296*(6*c+d)+36*(6*e+f)+(6*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 36*(6*a+b)+(6*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 46656*(6*a+b)+1296*(6*c+d)+36*(6*e+f)+(6*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix7 (a b c d e f g h : Nat)
    (ha : a<7) (hb : b<7) (hc : c<7) (hd : d<7)
    (he : e<7) (hf : f<7) (hg : g<7) (hh : h<7) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*7+n/256
    ((((p &&& 1095216660735)*(49+117649*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+2401*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 823543*a + 117649*b + 16807*c + 2401*d + 343*e + 49*f + 7*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 7*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (7*a+b) + 256*(1*(7*b+c) + 256*(7*c+d) + 65536*(7*d+e) + 16777216*(7*e+f) + 4294967296*(7*f+g) + 1099511627776*(7*g+h) + 281474976710656*(7*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 7*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(7*a+b) + 256*(7*b+c) + 65536*(7*c+d) + 16777216*(7*d+e)) + 4294967296*(1*(7*e+f) + 256*(7*f+g) + 65536*(7*g+h) + 16777216*(7*h)) := by ring
    have hlo : (1*(7*a+b) + 256*(7*b+c) + 65536*(7*c+d) + 16777216*(7*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(7*e+f) + 256*(7*f+g) + 65536*(7*g+h) + 16777216*(7*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(7*e+f) + 256*(7*f+g) + 65536*(7*g+h) + 16777216*(7*h)) = (7*e+f) + 256*(1*(7*f+g) + 256*(7*g+h) + 65536*(7*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 7*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(7*a+b) + 256*(7*b+c)) + 65536*(1*(7*c+d) + 256*(7*d+e) + 65536*(7*e+f) + 16777216*(7*f+g) + 4294967296*(7*g+h) + 1099511627776*(7*h)) := by ring
    have hlo : (1*(7*a+b) + 256*(7*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(7*c+d) + 256*(7*d+e) + 65536*(7*e+f) + 16777216*(7*f+g) + 4294967296*(7*g+h) + 1099511627776*(7*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(7*c+d) + 256*(7*d+e) + 65536*(7*e+f) + 16777216*(7*f+g) + 4294967296*(7*g+h) + 1099511627776*(7*h)) = (7*c+d) + 256*(1*(7*d+e) + 256*(7*e+f) + 65536*(7*f+g) + 16777216*(7*g+h) + 4294967296*(7*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 7*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(7*a+b) + 256*(7*b+c) + 65536*(7*c+d) + 16777216*(7*d+e) + 4294967296*(7*e+f) + 1099511627776*(7*f+g)) + 281474976710656*(1*(7*g+h) + 256*(7*h)) := by ring
    have hlo : (1*(7*a+b) + 256*(7*b+c) + 65536*(7*c+d) + 16777216*(7*d+e) + 4294967296*(7*e+f) + 1099511627776*(7*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*7+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(7*g+h) + 256*(7*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(7*g+h) + 256*(7*h)) = (7*g+h) + 256*(1*(7*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (7*a+b+4294967296*(7*e+f))*(49+117649*4294967296) +
      (7*c+d+4294967296*(7*g+h))*(1+2401*4294967296) =
      (49*(7*a+b)+(7*c+d)) +
      4294967296*(117649*(7*a+b)+2401*(7*c+d)+49*(7*e+f)+(7*g+h)) +
      18446744073709551616*(117649*(7*e+f)+2401*(7*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (49*(7*a+b)+(7*c+d)) +
      4294967296*(117649*(7*a+b)+2401*(7*c+d)+49*(7*e+f)+(7*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 49*(7*a+b)+(7*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 117649*(7*a+b)+2401*(7*c+d)+49*(7*e+f)+(7*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix8 (a b c d e f g h : Nat)
    (ha : a<8) (hb : b<8) (hc : c<8) (hd : d<8)
    (he : e<8) (hf : f<8) (hg : g<8) (hh : h<8) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*8+n/256
    ((((p &&& 1095216660735)*(64+262144*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+4096*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 2097152*a + 262144*b + 32768*c + 4096*d + 512*e + 64*f + 8*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 8*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (8*a+b) + 256*(1*(8*b+c) + 256*(8*c+d) + 65536*(8*d+e) + 16777216*(8*e+f) + 4294967296*(8*f+g) + 1099511627776*(8*g+h) + 281474976710656*(8*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 8*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(8*a+b) + 256*(8*b+c) + 65536*(8*c+d) + 16777216*(8*d+e)) + 4294967296*(1*(8*e+f) + 256*(8*f+g) + 65536*(8*g+h) + 16777216*(8*h)) := by ring
    have hlo : (1*(8*a+b) + 256*(8*b+c) + 65536*(8*c+d) + 16777216*(8*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(8*e+f) + 256*(8*f+g) + 65536*(8*g+h) + 16777216*(8*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(8*e+f) + 256*(8*f+g) + 65536*(8*g+h) + 16777216*(8*h)) = (8*e+f) + 256*(1*(8*f+g) + 256*(8*g+h) + 65536*(8*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 8*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(8*a+b) + 256*(8*b+c)) + 65536*(1*(8*c+d) + 256*(8*d+e) + 65536*(8*e+f) + 16777216*(8*f+g) + 4294967296*(8*g+h) + 1099511627776*(8*h)) := by ring
    have hlo : (1*(8*a+b) + 256*(8*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(8*c+d) + 256*(8*d+e) + 65536*(8*e+f) + 16777216*(8*f+g) + 4294967296*(8*g+h) + 1099511627776*(8*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(8*c+d) + 256*(8*d+e) + 65536*(8*e+f) + 16777216*(8*f+g) + 4294967296*(8*g+h) + 1099511627776*(8*h)) = (8*c+d) + 256*(1*(8*d+e) + 256*(8*e+f) + 65536*(8*f+g) + 16777216*(8*g+h) + 4294967296*(8*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 8*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(8*a+b) + 256*(8*b+c) + 65536*(8*c+d) + 16777216*(8*d+e) + 4294967296*(8*e+f) + 1099511627776*(8*f+g)) + 281474976710656*(1*(8*g+h) + 256*(8*h)) := by ring
    have hlo : (1*(8*a+b) + 256*(8*b+c) + 65536*(8*c+d) + 16777216*(8*d+e) + 4294967296*(8*e+f) + 1099511627776*(8*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*8+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(8*g+h) + 256*(8*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(8*g+h) + 256*(8*h)) = (8*g+h) + 256*(1*(8*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (8*a+b+4294967296*(8*e+f))*(64+262144*4294967296) +
      (8*c+d+4294967296*(8*g+h))*(1+4096*4294967296) =
      (64*(8*a+b)+(8*c+d)) +
      4294967296*(262144*(8*a+b)+4096*(8*c+d)+64*(8*e+f)+(8*g+h)) +
      18446744073709551616*(262144*(8*e+f)+4096*(8*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (64*(8*a+b)+(8*c+d)) +
      4294967296*(262144*(8*a+b)+4096*(8*c+d)+64*(8*e+f)+(8*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 64*(8*a+b)+(8*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 262144*(8*a+b)+4096*(8*c+d)+64*(8*e+f)+(8*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix9 (a b c d e f g h : Nat)
    (ha : a<9) (hb : b<9) (hc : c<9) (hd : d<9)
    (he : e<9) (hf : f<9) (hg : g<9) (hh : h<9) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*9+n/256
    ((((p &&& 1095216660735)*(81+531441*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+6561*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 4782969*a + 531441*b + 59049*c + 6561*d + 729*e + 81*f + 9*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 9*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (9*a+b) + 256*(1*(9*b+c) + 256*(9*c+d) + 65536*(9*d+e) + 16777216*(9*e+f) + 4294967296*(9*f+g) + 1099511627776*(9*g+h) + 281474976710656*(9*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 9*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(9*a+b) + 256*(9*b+c) + 65536*(9*c+d) + 16777216*(9*d+e)) + 4294967296*(1*(9*e+f) + 256*(9*f+g) + 65536*(9*g+h) + 16777216*(9*h)) := by ring
    have hlo : (1*(9*a+b) + 256*(9*b+c) + 65536*(9*c+d) + 16777216*(9*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(9*e+f) + 256*(9*f+g) + 65536*(9*g+h) + 16777216*(9*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(9*e+f) + 256*(9*f+g) + 65536*(9*g+h) + 16777216*(9*h)) = (9*e+f) + 256*(1*(9*f+g) + 256*(9*g+h) + 65536*(9*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 9*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(9*a+b) + 256*(9*b+c)) + 65536*(1*(9*c+d) + 256*(9*d+e) + 65536*(9*e+f) + 16777216*(9*f+g) + 4294967296*(9*g+h) + 1099511627776*(9*h)) := by ring
    have hlo : (1*(9*a+b) + 256*(9*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(9*c+d) + 256*(9*d+e) + 65536*(9*e+f) + 16777216*(9*f+g) + 4294967296*(9*g+h) + 1099511627776*(9*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(9*c+d) + 256*(9*d+e) + 65536*(9*e+f) + 16777216*(9*f+g) + 4294967296*(9*g+h) + 1099511627776*(9*h)) = (9*c+d) + 256*(1*(9*d+e) + 256*(9*e+f) + 65536*(9*f+g) + 16777216*(9*g+h) + 4294967296*(9*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 9*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(9*a+b) + 256*(9*b+c) + 65536*(9*c+d) + 16777216*(9*d+e) + 4294967296*(9*e+f) + 1099511627776*(9*f+g)) + 281474976710656*(1*(9*g+h) + 256*(9*h)) := by ring
    have hlo : (1*(9*a+b) + 256*(9*b+c) + 65536*(9*c+d) + 16777216*(9*d+e) + 4294967296*(9*e+f) + 1099511627776*(9*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*9+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(9*g+h) + 256*(9*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(9*g+h) + 256*(9*h)) = (9*g+h) + 256*(1*(9*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (9*a+b+4294967296*(9*e+f))*(81+531441*4294967296) +
      (9*c+d+4294967296*(9*g+h))*(1+6561*4294967296) =
      (81*(9*a+b)+(9*c+d)) +
      4294967296*(531441*(9*a+b)+6561*(9*c+d)+81*(9*e+f)+(9*g+h)) +
      18446744073709551616*(531441*(9*e+f)+6561*(9*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (81*(9*a+b)+(9*c+d)) +
      4294967296*(531441*(9*a+b)+6561*(9*c+d)+81*(9*e+f)+(9*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 81*(9*a+b)+(9*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 531441*(9*a+b)+6561*(9*c+d)+81*(9*e+f)+(9*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

set_option maxHeartbeats 100000 in
theorem packed8_radix10 (a b c d e f g h : Nat)
    (ha : a<10) (hb : b<10) (hc : c<10) (hd : d<10)
    (he : e<10) (hf : f<10) (hg : g<10) (hh : h<10) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*10+n/256
    ((((p &&& 1095216660735)*(100+1000000*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+10000*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = 10000000*a + 1000000*b + 100000*c + 10000*d + 1000*e + 100*f + 10*g + 1*h := by
  dsimp
  have hq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)/256 = b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h := by
    have heq : a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h = a + 256*(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by decide)]
    have haz : a/256 = 0 := Nat.div_eq_of_lt (by omega)
    omega
  rw [hq]
  rw [mask8_lanes, mask8_lanes]
  have hp0 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))%256 = 10*a+b := by
    clear hq
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (10*a+b) + 256*(1*(10*b+c) + 256*(10*c+d) + 65536*(10*d+e) + 16777216*(10*e+f) + 4294967296*(10*f+g) + 1099511627776*(10*g+h) + 281474976710656*(10*h)) := by ring
    rw [heq, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp1 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296%256 = 10*e+f := by
    clear hq hp0
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(10*a+b) + 256*(10*b+c) + 65536*(10*c+d) + 16777216*(10*d+e)) + 4294967296*(1*(10*e+f) + 256*(10*f+g) + 65536*(10*g+h) + 16777216*(10*h)) := by ring
    have hlo : (1*(10*a+b) + 256*(10*b+c) + 65536*(10*c+d) + 16777216*(10*d+e)) < 4294967296 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/4294967296 = (1*(10*e+f) + 256*(10*f+g) + 65536*(10*g+h) + 16777216*(10*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(10*e+f) + 256*(10*f+g) + 65536*(10*g+h) + 16777216*(10*h)) = (10*e+f) + 256*(1*(10*f+g) + 256*(10*g+h) + 65536*(10*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp2 : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536%256 = 10*c+d := by
    clear hq hp0 hp1
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(10*a+b) + 256*(10*b+c)) + 65536*(1*(10*c+d) + 256*(10*d+e) + 65536*(10*e+f) + 16777216*(10*f+g) + 4294967296*(10*g+h) + 1099511627776*(10*h)) := by ring
    have hlo : (1*(10*a+b) + 256*(10*b+c)) < 65536 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536 = (1*(10*c+d) + 256*(10*d+e) + 65536*(10*e+f) + 16777216*(10*f+g) + 4294967296*(10*g+h) + 1099511627776*(10*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [hdiv]
    have htail : (1*(10*c+d) + 256*(10*d+e) + 65536*(10*e+f) + 16777216*(10*f+g) + 4294967296*(10*g+h) + 1099511627776*(10*h)) = (10*c+d) + 256*(1*(10*d+e) + 256*(10*e+f) + 65536*(10*f+g) + 16777216*(10*g+h) + 4294967296*(10*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hp3 : (((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/65536)/4294967296%256 = 10*g+h := by
    clear hq hp0 hp1 hp2
    have heq : (a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h) = (1*(10*a+b) + 256*(10*b+c) + 65536*(10*c+d) + 16777216*(10*d+e) + 4294967296*(10*e+f) + 1099511627776*(10*f+g)) + 281474976710656*(1*(10*g+h) + 256*(10*h)) := by ring
    have hlo : (1*(10*a+b) + 256*(10*b+c) + 65536*(10*c+d) + 16777216*(10*d+e) + 4294967296*(10*e+f) + 1099511627776*(10*f+g)) < 281474976710656 := by omega
    have hdiv : ((a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h)*10+(b + 256*c + 65536*d + 16777216*e + 4294967296*f + 1099511627776*g + 281474976710656*h))/281474976710656 = (1*(10*g+h) + 256*(10*h)) := by
      rw [heq, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hlo]
      simp
    rw [Nat.div_div_eq_div_mul]
    norm_num only
    rw [hdiv]
    have htail : (1*(10*g+h) + 256*(10*h)) = (10*g+h) + 256*(1*(10*h)) := by ring
    rw [htail, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hp0,hp1,hp2,hp3]
  rw [← Nat.add_mod]
  have hs : (10*a+b+4294967296*(10*e+f))*(100+1000000*4294967296) +
      (10*c+d+4294967296*(10*g+h))*(1+10000*4294967296) =
      (100*(10*a+b)+(10*c+d)) +
      4294967296*(1000000*(10*a+b)+10000*(10*c+d)+100*(10*e+f)+(10*g+h)) +
      18446744073709551616*(1000000*(10*e+f)+10000*(10*g+h)) := by ring
  norm_num only at hs
  rw [hs, Nat.add_mul_mod_self_left]
  clear hq hp0 hp1 hp2 hp3 hs
  have hbnd : (100*(10*a+b)+(10*c+d)) +
      4294967296*(1000000*(10*a+b)+10000*(10*c+d)+100*(10*e+f)+(10*g+h)) <
      18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hbnd, Nat.add_mul_div_left _ _ (by decide)]
  have hlo : 100*(10*a+b)+(10*c+d) < 4294967296 := by omega
  rw [Nat.div_eq_of_lt hlo]
  simp only [Nat.zero_add]
  have hval : 1000000*(10*a+b)+10000*(10*c+d)+100*(10*e+f)+(10*g+h) < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hval]
  omega

theorem packed8_arithmetic (r a b c d e f g h : Nat)
    (hr : 2 ≤ r ∧ r ≤ 10)
    (ha : a<r) (hb : b<r) (hc : c<r) (hd : d<r)
    (he : e<r) (hf : f<r) (hg : g<r) (hh : h<r) :
    let n := a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h
    let p := n*r+n/256
    ((((p &&& 1095216660735)*(r^2+r^6*4294967296))%18446744073709551616 +
      (((p/65536) &&& 1095216660735)*(1+r^4*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296
       = r^7*a + r^6*b + r^5*c + r^4*d + r^3*e + r^2*f + r*g + 1*h := by
  have hcases : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 := by omega
  rcases hcases with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 
  · subst r
    simpa using packed8_radix2 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix3 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix4 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix5 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix6 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix7 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix8 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix9 a b c d e f g h ha hb hc hd he hf hg hh
  · subst r
    simpa using packed8_radix10 a b c d e f g h ha hb hc hd he hf hg hh

theorem parse8_packed (r : U32) (v : U64) (a b c d e f g h : Nat)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (ha : a<r.val) (hb : b<r.val) (hc : c<r.val) (hd : d<r.val)
    (he : e<r.val) (hf : f<r.val) (hg : g<r.val) (hh : h<r.val)
    (hv : v.val = 3472328296227680304 + 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h) :
    lexical_parse_integer_radix_harness.parse_8digits r v
      ⦃ out => out.val = r.val^7*a + r.val^6*b + r.val^5*c + r.val^4*d + r.val^3*e + r.val^2*f + r.val*g + 1*h ⦄ := by
  have hl : 3472328296227680304 ≤ v.val := by omega
  have hu : v.val ≤ 4123389851770370361 := by omega
  have hn : v.val-3472328296227680304 = 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h := by omega
  have heq := packed8_arithmetic r.val a b c d e f g h hr ha hb hc hd he hf hg hh
  have hs := parse8_arithmetic r v hr hl hu
  simpa only [hn, one_mul, heq] using hs

theorem parse8_value (r : U32) (v : U64)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (hv : LexicalParseIntegerRadixSpec.digits8 r.val v.val) :
    lexical_parse_integer_radix_harness.parse_8digits r v
      ⦃ out => out.val = LexicalParseIntegerRadixSpec.value8 r.val v.val ⦄ := by
  have hdigit (i : Nat) (hi : i < 8) :
      LexicalParseIntegerRadixSpec.byteAt v.val i - 48 < r.val := by
    have h := hv i hi
    simp only [LexicalParseIntegerRadixSpec.asciiDigit] at h
    omega
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  have h4 := hv 4 (by decide)
  have h5 := hv 5 (by decide)
  have h6 := hv 6 (by decide)
  have h7 := hv 7 (by decide)
  simp only [LexicalParseIntegerRadixSpec.asciiDigit, LexicalParseIntegerRadixSpec.byteAt] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  have hbound : v.val ≤ 18446744073709551615 := by scalar_tac
  have hp : v.val = 3472328296227680304 + 1*(v.val%256-48) + 256*(v.val/256%256-48) + 65536*(v.val/65536%256-48) + 16777216*(v.val/16777216%256-48) + 4294967296*(v.val/4294967296%256-48) + 1099511627776*(v.val/1099511627776%256-48) + 281474976710656*(v.val/281474976710656%256-48) + 72057594037927936*(v.val/72057594037927936%256-48) := by omega
  have h := parse8_packed r v _ _ _ _ _ _ _ _ hr (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 0 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 1 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 2 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 3 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 4 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 5 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 6 (by decide)) (by simpa [LexicalParseIntegerRadixSpec.byteAt] using hdigit 7 (by decide)) hp
  have heval : LexicalParseIntegerRadixSpec.value8 r.val v.val =
      r.val^7*(v.val%256-48) + r.val^6*(v.val/256%256-48) +
      r.val^5*(v.val/65536%256-48) + r.val^4*(v.val/16777216%256-48) +
      r.val^3*(v.val/4294967296%256-48) + r.val^2*(v.val/1099511627776%256-48) +
      r.val*(v.val/281474976710656%256-48) + (v.val/72057594037927936%256-48) := by
    simp [LexicalParseIntegerRadixSpec.value8, LexicalParseIntegerRadixSpec.wordValue,
      LexicalParseIntegerRadixSpec.textValue, LexicalParseIntegerRadixSpec.byteAt,
      List.range_succ]
    ring
  simpa only [heval, one_mul] using h

theorem parse8_value_success (r : U32) (v : U64)
    (hr : 2 ≤ r.val ∧ r.val ≤ 10)
    (hv : LexicalParseIntegerRadixSpec.digits8 r.val v.val) :
    ∃ out, lexical_parse_integer_radix_harness.parse_8digits r v = Result.ok out ∧
      out.val = LexicalParseIntegerRadixSpec.value8 r.val v.val :=
  result_spec_success (parse8_value r v hr hv)

end LexicalParseIntegerRadixProofs
