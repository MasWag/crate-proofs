import Specs
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result
namespace LexicalParseIntegerProofs

def repeated (c : Nat) : Nat → Nat
 | 0 => 0
 | n+1 => c+256*repeated c n

def highClear : Nat → Nat → Prop
 | 0, _ => True
 | n+1, v => v%256<128 ∧ highClear n (v/256)

def digits : Nat → Nat → Prop
 | 0, _ => True
 | n+1, v => (48≤v%256 ∧ v%256<58) ∧ digits n (v/256)

theorem repeated_bound (n c : Nat) (hc : c<256) : repeated c n < 256^n := by
 induction n with
 | zero => simp [repeated]
 | succ n ih => simp only [repeated, Nat.pow_succ]; omega

theorem byte_math (x : Nat) (hx : x<256) :
 ((x+70)%256<128 ∧ (x+208)%256<128) ↔ 48≤x ∧ x<58 := by omega

theorem recognition_arithmetic (n v : Nat) :
 (highClear n (v+repeated 70 n) ∧
  highClear n (v+256^n-repeated 48 n)) ↔ digits n v := by
 induction n generalizing v with
 | zero => simp [highClear, digits]
 | succ n ih =>
   have hb := repeated_bound n 48 (by decide)
   have hx : v%256<256 := Nat.mod_lt _ (by decide)
   have hdiv := Nat.mod_add_div v 256
   have hsublo : (v+256^(n+1)-repeated 48 (n+1))%256 = (v%256+208)%256 := by
     simp only [repeated, Nat.pow_succ]
     omega
   have haddlo : (v+repeated 70 (n+1))%256 = (v%256+70)%256 := by
     simp only [repeated]
     omega
   simp only [highClear, digits, haddlo, hsublo]
   constructor
   · rintro ⟨⟨ha, harest⟩, ⟨hs, hsrest⟩⟩
     have hbyte := (byte_math (v%256) hx).mp ⟨ha,hs⟩
     have haddhi : (v+repeated 70 (n+1))/256 = v/256+repeated 70 n := by
       simp only [repeated]; omega
     have hsubhi : (v+256^(n+1)-repeated 48 (n+1))/256 = v/256+256^n-repeated 48 n := by
       simp only [repeated, Nat.pow_succ]; omega
     rw [haddhi] at harest
     rw [hsubhi] at hsrest
     exact ⟨hbyte, (ih (v/256)).mp ⟨harest,hsrest⟩⟩
   · rintro ⟨hbyte,hrest⟩
     have hp := (byte_math (v%256) hx).mpr hbyte
     have hrest := (ih (v/256)).mpr hrest
     have haddhi : (v+repeated 70 (n+1))/256 = v/256+repeated 70 n := by
       simp only [repeated]; omega
     have hsubhi : (v+256^(n+1)-repeated 48 (n+1))/256 = v/256+256^n-repeated 48 n := by
       simp only [repeated, Nat.pow_succ]; omega
     rw [haddhi,hsubhi]
     exact ⟨⟨hp.1,hrest.1⟩,⟨hp.2,hrest.2⟩⟩

theorem byte_mask (x : Nat) (hx : x<256) :
 (x &&& 128 = 0) ↔ x<128 := by
 have hlo : (x &&& 128)%128 = 0 := by
   change (x &&& 128)%(2^7)=0
   rw [Nat.and_mod_two_pow]
   norm_num
 have hhi : (x &&& 128)/128 = x/128 := by
   change (x &&& 128)/(2^7)=x/128
   rw [Nat.and_div_two_pow]
   norm_num only
   change (x/128) &&& (2^1-1) = x/128
   rw [Nat.and_two_pow_sub_one_eq_mod]
   omega
 have hd := Nat.mod_add_div (x &&& 128) 128
 omega

theorem highClear_mask (n v : Nat) :
 v &&& repeated 128 n = 0 ↔ highClear n v := by
 induction n generalizing v with
 | zero => simp [repeated,highClear]
 | succ n ih =>
   have hmlo : repeated 128 (n+1)%256 = 128 := by
     simp [repeated,Nat.add_mul_mod_self_left]
   have hmhi : repeated 128 (n+1)/256 = repeated 128 n := by
     simp [repeated,Nat.add_mul_div_left _ _ (show 0<256 by decide)]
   have hlo : (v &&& repeated 128 (n+1))%256 = (v%256)&&&128 := by
     change (v &&& repeated 128 (n+1))%(2^8) = _
     rw [Nat.and_mod_two_pow]
     norm_num only
     rw [hmlo]
   have hhi : (v &&& repeated 128 (n+1))/256 = (v/256)&&&repeated 128 n := by
     change (v &&& repeated 128 (n+1))/(2^8) = _
     rw [Nat.and_div_two_pow]
     norm_num only
     rw [hmhi]
   have hd := Nat.mod_add_div (v &&& repeated 128 (n+1)) 256
   have hz : v &&& repeated 128 (n+1) = 0 ↔
       (v%256)&&&128 = 0 ∧ (v/256)&&&repeated 128 n=0 := by omega
   rw [hz, byte_mask _ (Nat.mod_lt _ (by decide)), ih]
   rfl

theorem digits_spec (n v : Nat) :
 digits n v ↔ LexicalParseIntegerSpec.wordDigits 10 n v := by
 induction n generalizing v with
 | zero => simp [digits,LexicalParseIntegerSpec.wordDigits]
 | succ n ih =>
   have hshift (i : Nat) : LexicalParseIntegerSpec.byteAt (v/256) i =
       LexicalParseIntegerSpec.byteAt v (i+1) := by
     simp [LexicalParseIntegerSpec.byteAt,Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm]
   simp only [digits, ih, LexicalParseIntegerSpec.wordDigits]
   constructor
   · rintro ⟨h0,hs⟩ i hi
     cases i with
     | zero => simpa [LexicalParseIntegerSpec.asciiDigit,LexicalParseIntegerSpec.byteAt] using h0
     | succ i => rw [←hshift]; exact hs i (by omega)
   · intro h
     constructor
     · simpa [LexicalParseIntegerSpec.asciiDigit,LexicalParseIntegerSpec.byteAt] using h 0 (by omega)
     · intro i hi; rw [hshift]; exact h (i+1) (by omega)

theorem mask_wrap (n x : Nat) :
 (x%256^n)&&&repeated 128 n = x&&&repeated 128 n := by
 have hb := repeated_bound n 128 (by decide)
 have hpow : 256^n = 2^(8*n) := by
   change (2^8)^n = 2^(8*n)
   rw [Nat.pow_mul]
 have h := Nat.and_mod_two_pow (a:=x) (b:=repeated 128 n) (n:=8*n)
 rw [←hpow] at h
 rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hb), Nat.mod_eq_of_lt hb] at h
 exact h.symm

theorem recognition_mask (n v : Nat) :
 (((v+repeated 70 n)%256^n ||| (v+256^n-repeated 48 n)%256^n) &&& repeated 128 n = 0) ↔
 LexicalParseIntegerSpec.wordDigits 10 n v := by
 rw [Nat.and_or_distrib_right,Nat.or_eq_zero_iff,mask_wrap,mask_wrap,
     highClear_mask,highClear_mask,recognition_arithmetic,digits_spec]

end LexicalParseIntegerProofs
