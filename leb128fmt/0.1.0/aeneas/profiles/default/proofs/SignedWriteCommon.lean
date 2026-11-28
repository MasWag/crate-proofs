import ProofsSignedWriterGuards

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow

namespace leb128fmt.sliceProof

theorem scalar_eq_of_val {ty : UScalarTy} {x y : UScalar ty} (h : x.val = y.val) :
    x = y := UScalar.eq_imp x y h

structure SignedWriterLaws {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) : Prop extends SignedGuardLaws ops val storage where
  equal : ∀ x y, ops.eq.eq x y = ok (decide (val x = val y))
  payload : ∀ x mask, val mask = 127 →
    ∃ digit, ops.mask.bitand x mask = ok digit ∧ val digit = val x % 128
  shiftSeven : ∀ x,
    ∃ rest, ops.shiftAssign.shr_assign x 7#u32 = ok rest ∧ val rest = val x / 128
  narrowPayload : ∀ x, 0 ≤ val x → val x < 128 →
    ∃ byte, ops.narrow.try_from x = ok (.Ok byte) ∧ (byte.val : Int) = val x

abbrev SignedFits (value : Int) (index : Nat) : Prop :=
  -(64 * 128^index) ≤ value ∧ value < (64 * 128^index : Int)

def signedDigit (value : Int) (index : Nat) : Nat :=
  (value / 128^index % 128).toNat

def signedShortestByte (value : Int) (index : Nat) : Nat :=
  signedDigit value index + if SignedFits value index then 0 else 128

def signedFixedByte (value : Int) (count index : Nat) : Nat :=
  signedDigit value index + if index + 1 < count then 128 else 0

def sliceByte (bytes : Slice U8) (index : Nat) : Nat := (bytes.val[index]?.getD 0#u8).val

def SignedWritten (byte : Nat → Nat) (before : Slice U8) (start count : Nat)
    (after : Slice U8) : Prop :=
  after.val.length = before.val.length ∧
  ∀ i, i < before.val.length →
    sliceByte after i = if start ≤ i ∧ i < start + count then byte (i - start) else sliceByte before i

theorem sliceByte_set (out : Slice U8) (idx : Usize) (b : U8) (i : Nat)
    (hi : i < out.val.length) :
    sliceByte (out.set idx b) i = if i = idx.val then b.val else sliceByte out i := by
  simp only [sliceByte, Slice.set_val_eq, List.getElem?_set]
  split <;> simp_all [eq_comm]

theorem written_empty (byte : Nat → Nat) (before : Slice U8) (start : Nat) :
    SignedWritten byte before start 0 before := by
  refine ⟨rfl, ?_⟩
  intro i hi
  rw [ite_eq_right (by omega)]

theorem written_next {byte : Nat → Nat} {before after : Slice U8} {start : Nat}
    {idx : Usize} {b : U8} (hpos : start ≤ idx.val)
    (hwrite : SignedWritten byte before start (idx.val - start) after)
    (hb : b.val = byte (idx.val - start)) :
    SignedWritten byte before start (idx.val + 1 - start) (after.set idx b) := by
  obtain ⟨hlen, hbytes⟩ := hwrite
  refine ⟨by simpa [Slice.set_val_eq] using hlen, ?_⟩
  intro i hi
  rw [sliceByte_set _ _ _ _ (by omega), hbytes i hi]
  by_cases he : i = idx.val
  · rw [he, ite_eq_left rfl, ite_eq_left (by omega)]
    exact hb
  · rw [ite_eq_right he]
    have hp : (start ≤ i ∧ i < start + (idx.val - start)) ↔
        start ≤ i ∧ i < start + (idx.val + 1 - start) := by omega
    simp only [hp]

theorem fits_rest (x : Int) (index : Nat) :
    SignedFits x index ↔ -64 ≤ x / 128^index ∧ x / 128^index < 64 := by
  rw [Int.le_ediv_iff_mul_le (by positivity), Int.ediv_lt_iff_lt_mul (by positivity)]
  simp [SignedFits]

theorem next_rest (x : Int) (index : Nat) :
    x / (128^index : Int) / 128 = x / 128^(index+1) := by
  rw [Int.ediv_ediv_of_nonneg (by positivity), Int.pow_succ]

theorem end_condition (x : Int) :
    (-64 ≤ x ∧ x < 64) ↔
      (x / 128 = 0 ∧ x % 128 < 64) ∨ (x / 128 = -1 ∧ 64 ≤ x % 128) := by omega

theorem sign_mask_val (b : U8) (hb : b.val < 128) :
    (b.val &&& 64) = 0 ↔ b.val < 64 := by
  have hdiv := @Nat.and_div_two_pow b.val 64 6
  have hmod := @Nat.and_mod_two_pow b.val 64 6
  change (b.val &&& 64) / 64 = (b.val / 64) &&& 1 at hdiv
  change (b.val &&& 64) % 64 = (b.val % 64) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  omega

theorem sign_mask (b : U8) (hb : b.val < 128) :
    (b &&& 64#u8 = 0#u8) ↔ b.val < 64 :=
  ⟨fun h => (sign_mask_val b hb).mp (congrArg UScalar.val h),
    fun h => scalar_eq_of_val ((sign_mask_val b hb).mpr h)⟩

theorem continuation_digit (b : U8) (hb : b.val < 128) :
    (b ||| 128#u8).val = b.val + 128 := by
  rw [UScalar.val_or]
  exact Nat.or_two_pow_eq_add_of_lt (n := 7) hb

theorem digit_step {T E : Type} (ops : SignedGuardOps T E) (val : T → Int)
    (storage : Nat) (laws : SignedWriterLaws ops val storage) (rest : T) :
    ∃ mask digit byte next,
      ops.fromSignedByte.«from» 127#i8 = ok mask ∧
      ops.mask.bitand rest mask = ok digit ∧ ops.narrow.try_from digit = ok (.Ok byte) ∧
      ops.shiftAssign.shr_assign rest 7#u32 = ok next ∧
      (byte.val : Int) = val rest % 128 ∧ val next = val rest / 128 := by
  obtain ⟨mask, hmask, hmaskVal⟩ := laws.signedByte 127#i8
  obtain ⟨digit, hdigit, hdigitVal⟩ := laws.payload rest mask hmaskVal
  obtain ⟨byte, hbyte, hbyteVal⟩ := laws.narrowPayload digit (by rw [hdigitVal]; omega)
    (by rw [hdigitVal]; omega)
  obtain ⟨next, hnext, hnextVal⟩ := laws.shiftSeven rest
  exact ⟨mask, digit, byte, next, hmask, hdigit, hbyte, hnext, hbyteVal.trans hdigitVal, hnextVal⟩


theorem signed_guard_quotient {value bound : Int} (hpositive : 0 < bound)
    (h : -bound ≤ value ∧ value < bound) :
    value / bound = 0 ∨ value / bound = -1 := by
  have hlo : -1 ≤ value / bound := (Int.le_ediv_iff_mul_le hpositive).mpr (by simpa using h.1)
  have hhi : value / bound < 1 := (Int.ediv_lt_iff_lt_mul hpositive).mpr (by simpa using h.2)
  omega

abbrev SignedGuardAccepts (storage width : Nat) (value : Int) : Prop :=
  storage ≤ width ∨ -(2^width : Int) ≤ value ∧ value < (2^width : Int)


theorem fixed_fits_of_representable (width : Nat) (value : Int) (hwidth : 0 < width)
    (hrange : -(2^(width - 1) : Int) ≤ value ∧ value < (2^(width - 1) : Int)) :
    SignedFits value ((width + 6) / 7 - 1) := by
  let index := (width + 6) / 7 - 1
  have hwidth' : width - 1 ≤ 6 + 7 * index := by dsimp [index]; omega
  have hboundNat : 2^(width - 1) ≤ 2^(6 + 7 * index) :=
    Nat.pow_le_pow_right (by decide) hwidth'
  have hbound : (2^(width - 1) : Int) ≤ 2^(6 + 7 * index) := by exact_mod_cast hboundNat
  have hpow : (2 ^ (6 + 7 * index) : Int) = 64 * (128 : Int)^index := by
    rw [Int.pow_add, Int.pow_mul]
    rfl
  rw [hpow] at hbound
  change -(64 * 128^index) ≤ value ∧ value < (64 * 128^index : Int)
  omega

theorem guard_accepts_of_representable (storage width : Nat) (value : Int)
    (hrange : -(2^(width - 1) : Int) ≤ value ∧ value < (2^(width - 1) : Int)) :
    SignedGuardAccepts storage width value := by
  have hnat : 2^(width - 1) ≤ 2^width := Nat.pow_le_pow_right (by decide) (by omega)
  have hbound : (2^(width - 1) : Int) ≤ (2^width : Int) := by exact_mod_cast hnat
  exact Or.inr ⟨by omega, by omega⟩

end leb128fmt.sliceProof
