import Aeneas

open Aeneas Aeneas.Std
namespace leb128fmt.signedMath

theorem pow_radix (i : Nat) : 2 ^ (7 * i) = 128 ^ i := by
  rw [Nat.pow_mul]

theorem decode_append {acc digit index : Nat} (ha : acc < 128 ^ index)
    (hd : digit < 128) : acc + digit * 128 ^ index < 128 ^ (index + 1) := by
  rw [Nat.pow_succ]
  have hp : 0 < 128 ^ index := by positivity
  nlinarith

theorem bv_or_chunk {w s : Nat} (a b : BitVec w) (ha : a.toNat < 2^s) :
    (a ||| (b <<< s)) = BitVec.ofNat w (a.toNat + b.toNat * 2^s) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  calc
    _ = (a.toNat % 2^w) ||| ((b.toNat <<< s) % 2^w) := by rw [Nat.mod_eq_of_lt a.isLt]
    _ = (a.toNat ||| (b.toNat <<< s)) % 2^w := (Nat.or_mod_two_pow (n := w)).symm
    _ = _ := by
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

theorem bv_sign_extend {w s : Nat} (a : BitVec w) (ha : a.toNat < 2^s) :
    (a ||| (BitVec.allOnes w <<< s)) =
      BitVec.ofInt w ((a.toNat : Int) - (2^s : Nat)) := by
  rw [bv_or_chunk _ _ ha, BitVec.toNat_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have hw : 0 < 2^w := by positivity
  have hcalc : ((a.toNat + (2^w - 1) * 2^s : Nat) : Int) =
      (a.toNat : Int) - (2^s : Nat) + (2^s : Nat) * (2^w : Nat) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2^w)]
    ring
  calc
    _ = (((a.toNat + (2^w - 1) * 2^s : Nat) : Int) % (2^w : Nat)).toNat := by
      rw [Int.toNat_emod (by positivity) (by positivity)]
      simp only [Int.toNat_natCast]
    _ = _ := by rw [hcalc]; simp

theorem bv_sign_wrap {w k : Nat} (a : Nat) (hk : w ≤ 7*k) :
    BitVec.ofNat w a = BitVec.ofInt w ((a : Int) - (128^k : Nat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  calc
    _ = ((a : Int) % (2^w : Nat)).toNat := by
      rw [Int.toNat_emod (by positivity) (by positivity)]
      simp only [Int.toNat_natCast]
    _ = _ := by
      rw [← pow_radix, show 7*k = (7*k - w) + w by omega, pow_add]
      push_cast
      rw [Int.sub_mul_emod_self_right]

end leb128fmt.signedMath
