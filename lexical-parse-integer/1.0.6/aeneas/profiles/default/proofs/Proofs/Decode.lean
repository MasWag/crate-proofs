import Specs

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result

namespace LexicalParseIntegerProofs

theorem parse4_arithmetic (v : U32)
    (hl : 808464432 ≤ v.val) (hu : v.val ≤ 960051513) :
    lexical_parse_integer_swar_harness.parse_4digits v
      ⦃ out => out.val = (((v.val - 808464432)*10 + (v.val-808464432)/256)%128)*100 +
        (((v.val - 808464432)*10 + (v.val-808464432)/256)/65536)%128 ⦄ := by
  unfold lexical_parse_integer_swar_harness.parse_4digits
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
    omega
theorem parse4_packed_decimal (v : U32) (a b c d : Nat)
    (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10)
    (hv : v.val = 808464432 + a + 256*b + 65536*c + 16777216*d) :
    lexical_parse_integer_swar_harness.parse_4digits v
      ⦃ out => out.val = 1000*a + 100*b + 10*c + d ⦄ := by
  have hl : 808464432 ≤ v.val := by omega
  have hu : v.val ≤ 960051513 := by omega
  have hn : v.val - 808464432 = a + 256*b + 65536*c + 16777216*d := by omega
  have he := LexicalParseIntegerSpec.decimal4PackedArithmetic a b c d ha hb hc hd
  have h := parse4_arithmetic v hl hu
  simpa only [hn, he] using h

theorem parse4_decimal (v : U32)
    (hv : LexicalParseIntegerSpec.decimal4Digits v.val) :
    lexical_parse_integer_swar_harness.parse_4digits v
      ⦃ out => out.val = LexicalParseIntegerSpec.decimal4Value v.val ⦄ := by
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [LexicalParseIntegerSpec.asciiDigit, LexicalParseIntegerSpec.byteAt] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have hbound : v.val ≤ 4294967295 := by scalar_tac
  have hp : v.val = 808464432 + (v.val % 256-48) + 256*(v.val/256%256-48) +
      65536*(v.val/65536%256-48) + 16777216*(v.val/16777216%256-48) := by omega
  have h := parse4_packed_decimal v _ _ _ _ (by omega) (by omega) (by omega) (by omega) hp
  simpa [LexicalParseIntegerSpec.decimal4Value, LexicalParseIntegerSpec.wordValue,
    LexicalParseIntegerSpec.textValue, LexicalParseIntegerSpec.byteAt, List.range_succ,
    Nat.mul_add, Nat.add_mul, ←Nat.mul_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

unseal Result in
theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun value _ hp => ⟨value, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem parse4_decimal_success (v : U32)
    (hv : LexicalParseIntegerSpec.decimal4Digits v.val) :
    ∃ out, lexical_parse_integer_swar_harness.parse_4digits v = Result.ok out ∧
      out.val = LexicalParseIntegerSpec.decimal4Value v.val :=
  result_spec_success (parse4_decimal v hv)

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

theorem parse8_arithmetic (v : U64)
    (hl : 3472328296227680304 ≤ v.val) (hu : v.val ≤ 4123389851770370361) :
    lexical_parse_integer_swar_harness.parse_8digits v
      ⦃ out => out.val =
        ((((((v.val-3472328296227680304)*10 + (v.val-3472328296227680304)/256) &&& 1095216660735)
            * (100+1000000*4294967296))%18446744073709551616 +
         (((((v.val-3472328296227680304)*10 + (v.val-3472328296227680304)/256)/65536) &&& 1095216660735)
            * (1+10000*4294967296))%18446744073709551616)%18446744073709551616/4294967296)%4294967296 ⦄ := by
  unfold lexical_parse_integer_swar_harness.parse_8digits
  step*
  simp only [i9_post, UScalar.cast_val_eq, i8_post,
    i7_post, core.num.U64.wrapping_add_val_eq, v11_post, v21_post,
    core.num.U64.wrapping_mul_val_eq, i4_post, i6_post, UScalar.val_and,
    UScalar.ofNatCore_val_eq, i5_post, v2_post, i2_post, i3_post, v1_post,
    mul1_post, mul2_post, i_post, i1_post, radix6_post, radix4_post, radix2_post,
    radix_post, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UScalar.size, UScalarTy.numBits, U64.size_eq]
  norm_num
  omega

set_option maxHeartbeats 100000 in
theorem decimal8_packed_arithmetic (a b c d e f g h : Nat)
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

theorem parse8_packed_decimal (v : U64) (a b c d e f g h : Nat)
    (ha : a<10) (hb : b<10) (hc : c<10) (hd : d<10)
    (he : e<10) (hf : f<10) (hg : g<10) (hh : h<10)
    (hv : v.val = 3472328296227680304 + 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h) :
    lexical_parse_integer_swar_harness.parse_8digits v
      ⦃ out => out.val = 10000000*a + 1000000*b + 100000*c + 10000*d + 1000*e + 100*f + 10*g + 1*h ⦄ := by
  have hl : 3472328296227680304 ≤ v.val := by omega
  have hu : v.val ≤ 4123389851770370361 := by omega
  have hn : v.val-3472328296227680304 = 1*a + 256*b + 65536*c + 16777216*d + 4294967296*e + 1099511627776*f + 281474976710656*g + 72057594037927936*h := by omega
  have heq := decimal8_packed_arithmetic a b c d e f g h ha hb hc hd he hf hg hh
  have hs := parse8_arithmetic v hl hu
  simpa only [hn, one_mul, heq] using hs

theorem parse8_decimal (v : U64)
    (hv : LexicalParseIntegerSpec.decimal8Digits v.val) :
    lexical_parse_integer_swar_harness.parse_8digits v
      ⦃ out => out.val = LexicalParseIntegerSpec.decimal8Value v.val ⦄ := by
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  have h4 := hv 4 (by decide)
  have h5 := hv 5 (by decide)
  have h6 := hv 6 (by decide)
  have h7 := hv 7 (by decide)
  simp only [LexicalParseIntegerSpec.asciiDigit, LexicalParseIntegerSpec.byteAt] at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  have hbound : v.val ≤ 18446744073709551615 := by scalar_tac
  have hp : v.val = 3472328296227680304 + 1*(v.val%256-48) + 256*(v.val/256%256-48) + 65536*(v.val/65536%256-48) + 16777216*(v.val/16777216%256-48) + 4294967296*(v.val/4294967296%256-48) + 1099511627776*(v.val/1099511627776%256-48) + 281474976710656*(v.val/281474976710656%256-48) + 72057594037927936*(v.val/72057594037927936%256-48) := by omega
  have h := parse8_packed_decimal v _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hp
  simpa [LexicalParseIntegerSpec.decimal8Value, LexicalParseIntegerSpec.wordValue,
    LexicalParseIntegerSpec.textValue, LexicalParseIntegerSpec.byteAt, List.range_succ,
    Nat.mul_add, Nat.add_mul, ←Nat.mul_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem parse8_decimal_success (v : U64)
    (hv : LexicalParseIntegerSpec.decimal8Digits v.val) :
    ∃ out, lexical_parse_integer_swar_harness.parse_8digits v = Result.ok out ∧
      out.val = LexicalParseIntegerSpec.decimal8Value v.val :=
  result_spec_success (parse8_decimal v hv)

end LexicalParseIntegerProofs