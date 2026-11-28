import Signed32
import SignedDecodeMath

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow

namespace leb128fmt.signed32

open leb128fmt.signedMath

private theorem total_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

private theorem scalar_eq_of_val {ty : UScalarTy} {a b : UScalar ty} (h : a.val = b.val) :
    a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      congr 1
      exact BitVec.eq_of_toNat_eq h

private theorem mask_payload (x : Nat) : x &&& 127 = x % 128 := by
  exact Nat.and_two_pow_sub_one_eq_mod x 7

private theorem set_continuation {x : Nat} (h : x < 128) : x ||| 128 = x + 128 :=
  Nat.or_two_pow_eq_add_of_lt (n := 7) h

abbrev Bytes32 := Array U8 5#usize

def payloadDigit (x i : Nat) : Nat := x / 128 ^ i % 128

def encodedByte (x i : Nat) (more : Bool) : Nat :=
  payloadDigit x i + if more then 128 else 0

def byteAt (bytes : Bytes32) (i : Nat) : Nat := (bytes.val[i]?.getD 0#u8).val

private theorem byteAt_set (bytes : Bytes32) (idx : Usize) (value : U8) (i : Nat)
    (hi : i < 5) :
    byteAt (bytes.set idx value) i = if i = idx.val then value.val else byteAt bytes i := by
  have hlen : bytes.val.length = 5 := by have := bytes.property; scalar_tac
  simp only [byteAt, Array.set_val_eq, List.getElem?_set, hlen]
  split <;> simp_all [eq_comm]

private theorem byteAt_repeat (i : Nat) (_hi : i < 5) :
    byteAt (Array.repeat 5#usize 0#u8) i = 0 := by
  simp only [byteAt, Array.repeat_val, List.getElem?_replicate]
  split <;> rfl


private theorem int_scalar_eq_of_val {ty : IScalarTy} {a b : IScalar ty} (h : a.val = b.val) :
    a = b := by
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      congr 1
      exact BitVec.eq_of_toInt_eq h

private theorem signed_digit (value masked : I32) (digit : U8)
    (hmask : masked.bv = value.bv &&& 127#32)
    (hcast : digit = IScalar.hcast .U8 masked) :
    digit.val = (value.val % 128).toNat := by
  have hbv : masked.bv.toNat = value.bv.toNat % 128 := by
    rw [hmask, BitVec.toNat_and]
    exact mask_payload _
  have hpos := Nat.mod_lt value.bv.toNat (by decide : 0 < 128)
  have hm : masked.val = (value.bv.toNat % 128 : Nat) := by
    rw [IScalar.val, BitVec.toInt_eq_toNat_bmod, hbv]
    change (↑(value.bv.toNat % 128) : Int).bmod 4294967296 = _
    rw [Int.bmod_eq_emod_of_lt]
    · exact Int.emod_eq_of_lt (by positivity) (by omega)
    · rw [Int.emod_eq_of_lt (by positivity) (by omega)]
      omega
  rw [hcast, IScalar.hcast_val_eq, hm]
  change ((value.bv.toNat % 128 : Nat) % (256 : Int)).toNat = _
  rw [Int.emod_eq_of_lt (by positivity) (by omega)]
  change value.bv.toNat % 128 = _
  have hp : (128 : Int) ∣ 4294967296 := ⟨33554432, by decide⟩
  have hh : value.val % 128 = (value.bv.toNat : Int) % 128 := by
    rw [IScalar.val, BitVec.toInt_eq_toNat_bmod]
    change (value.bv.toNat : Int).bmod 4294967296 % 128 = _
    calc
      _ = ((value.bv.toNat : Int).bmod 4294967296 % 4294967296) % 128 :=
        (Int.emod_emod_of_dvd _ hp).symm
      _ = ((value.bv.toNat : Int) % 4294967296) % 128 := by
        exact congrArg (fun n : Int => n % 128) (Int.bmod_emod (m := 4294967296))
      _ = _ := Int.emod_emod_of_dvd _ hp
  rw [hh, Int.toNat_emod (by positivity) (by decide)]
  rfl

private theorem mask_sign (b flag : U8) (h : flag.val = (b &&& 64#u8).val)
    (hb : b.val < 128) : flag = 0#u8 ↔ b.val < 64 := by
  have hdiv := @Nat.and_div_two_pow b.val 64 6
  have hmod := @Nat.and_mod_two_pow b.val 64 6
  change (b.val &&& 64) / 64 = (b.val / 64) &&& 1 at hdiv
  change (b.val &&& 64) % 64 = (b.val % 64) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  have hf : flag.val = b.val &&& 64 := by simpa using h
  have he : flag.val = 0 ↔ b.val < 64 := by omega
  exact ⟨fun heq => he.mp (congrArg UScalar.val heq),
    fun hl => scalar_eq_of_val (he.mpr hl)⟩

def SignedFits (x : Int) (i : Nat) : Prop := -64 ≤ x / 128 ^ i ∧ x / 128 ^ i < 64

def signedByte (x : Int) (i : Nat) (more : Bool) : Nat :=
  (x / 128 ^ i % 128).toNat + if more then 128 else 0

def SignedCanonicalEncoding (x : Int) (bytes : Bytes32) (k : Nat) : Prop :=
  0 < k ∧ k ≤ 5 ∧ SignedFits x (k - 1) ∧ (1 < k → ¬SignedFits x (k - 2)) ∧
  ∀ i, i < 5 → byteAt bytes i = if i < k then signedByte x i (decide (i + 1 < k)) else 0

private def SignedEncodingInvariant (x : I32) (state : I32 × Bytes32 × Usize) : Prop :=
  state.2.2.val < 5 ∧
  state.1.val = x.val / 128 ^ state.2.2.val ∧
  (0 < state.2.2.val → ¬SignedFits x.val (state.2.2.val - 1)) ∧
  ∀ i, i < 5 → byteAt state.2.1 i =
    if i < state.2.2.val then signedByte x.val i true else 0

private def Terminal (x : I32) (out : Bytes32 × Usize × U8) : Prop :=
  out.2.1.val < 5 ∧
  SignedFits x.val out.2.1.val ∧
  (0 < out.2.1.val → ¬SignedFits x.val (out.2.1.val - 1)) ∧
  out.2.2.val = signedByte x.val out.2.1.val false ∧
  ∀ i, i < 5 → byteAt out.1 i =
    if i < out.2.1.val then signedByte x.val i true else 0

private theorem fits_last (x : I32) : SignedFits x.val 4 := by
  have hlo : -(2^31 : Int) ≤ x.val := by scalar_tac
  have hhi : x.val < 2^31 := by scalar_tac
  unfold SignedFits
  change -64 ≤ x.val / 268435456 ∧ x.val / 268435456 < 64
  omega

private theorem fits_iff_step (value : Int) :
    (-64 ≤ value ∧ value < 64) ↔
      (value / 128 = 0 ∧ (value % 128).toNat < 64) ∨
      (value / 128 = -1 ∧ 64 ≤ (value % 128).toNat) := by omega

private theorem signed_continue (x value1 : I32) (bytes a : Bytes32) (idx index1 : Usize)
    (b i3 : U8) (hidx : idx.val < 5)
    (hnext : value1.val = x.val / 128 ^ (idx.val + 1))
    (hn : ¬SignedFits x.val idx.val)
    (hbytes : ∀ j, j < 5 → byteAt bytes j =
      if j < idx.val then signedByte x.val j true else 0)
    (hb : b.val = signedByte x.val idx.val false) (hsmall : b.val < 128)
    (hi3 : i3.val = (b ||| 128#u8).val) (ha : a = bytes.set idx i3)
    (hi : index1.val = idx.val + 1) :
    SignedEncodingInvariant x (value1, a, index1) ∧ 5 - index1.val < 5 - idx.val := by
  have hbound : idx.val + 1 < 5 := by
    by_contra! h
    have he : idx.val = 4 := by omega
    exact hn (he ▸ fits_last x)
  have hc : i3.val = signedByte x.val idx.val true := by
    rw [hi3, UScalar.val_or]
    change b.val ||| 128 = _
    rw [set_continuation hsmall, hb]
    simp [signedByte]
  simp only [SignedEncodingInvariant, hi]
  refine ⟨⟨hbound, hnext, ?_, ?_⟩, by omega⟩
  · intro _
    simpa using hn
  · intro j hj
    rw [ha, byteAt_set _ _ _ _ hj, hbytes _ hj]
    by_cases hji : j = idx.val
    · simp [hji, hc]
    · have hlt : j < idx.val + 1 ↔ j < idx.val := by omega
      simp [hji, hlt]

private theorem encode_signed_loop_spec (x : I32) :
    WP.spec (encode_s32_loop2 x (Array.repeat 5#usize 0#u8) 0#usize) (Terminal x) := by
  unfold encode_s32_loop2
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.2.val)
    (inv := SignedEncodingInvariant x)
  · rintro ⟨value, bytes, idx⟩ ⟨hidx, hvalue, hprevious, hbytes⟩
    dsimp at *
    unfold encode_s32_loop2.body
    step*
    all_goals
      have hd := signed_digit value i b i_post1 b_post
      have hsmall : b.val < 128 := by omega
      have hq : value1.val = value.val / 128 := by
        rw [value1_post, Int.shiftRight_eq_div_pow]
        rfl
      have hnext : value1.val = x.val / 128 ^ (idx.val + 1) := by
        rw [hq, hvalue, Int.ediv_ediv_of_nonneg (by positivity), pow_succ]
      have hfinish : SignedFits x.val idx.val ↔
          (value1 = 0#i32 ∧ b.val < 64) ∨ (value1 = (-1)#i32 ∧ 64 ≤ b.val) := by
        unfold SignedFits
        rw [← hvalue, fits_iff_step, ← hq, ← hd]
        have hz : value1.val = 0 ↔ value1 = 0#i32 :=
          ⟨fun h => int_scalar_eq_of_val h, fun h => congrArg IScalar.val h⟩
        have hn : value1.val = -1 ↔ value1 = (-1)#i32 :=
          ⟨fun h => int_scalar_eq_of_val h, fun h => congrArg IScalar.val h⟩
        rw [hz, hn]
      have hb : b.val = signedByte x.val idx.val false := by
        rw [hd, hvalue]
        simp [signedByte]
    · have h0 : value1 = 0#i32 := by assumption
      have hsign : i1 = 0#u8 := by assumption
      have hlt := (mask_sign b i1 i1_post hsmall).mp hsign
      exact ⟨hidx, hfinish.mpr (Or.inl ⟨h0, hlt⟩), hprevious, hb, hbytes⟩
    · have h0 : value1 = 0#i32 := by assumption
      have hsign : i1 ≠ 0#u8 := by assumption
      have hn : ¬SignedFits x.val idx.val := by
        have hnl : ¬b.val < 64 := fun h => hsign ((mask_sign b i1 i1_post hsmall).mpr h)
        rw [hfinish, h0]
        simp
        omega
      rw [← h0]
      exact signed_continue x value1 bytes a idx index1 b i3 hidx hnext hn hbytes hb hsmall
        i3_post a_post index1_post
    · have hm : value1 = (-1)#i32 := by assumption
      have hsign : (i2 != 0#u8) = true := by assumption
      have hsign' : i2 ≠ 0#u8 := by simpa using hsign
      have hge : 64 ≤ b.val := Nat.le_of_not_gt fun h =>
        hsign' ((mask_sign b i2 i2_post hsmall).mpr h)
      exact ⟨hidx, hfinish.mpr (Or.inr ⟨hm, hge⟩), hprevious, hb, hbytes⟩
    · have hm : value1 = (-1)#i32 := by assumption
      have hsign : ¬(i2 != 0#u8) = true := by assumption
      have hsign' : i2 = 0#u8 := by
        apply scalar_eq_of_val
        simpa using hsign
      have hlt := (mask_sign b i2 i2_post hsmall).mp hsign'
      have hn : ¬SignedFits x.val idx.val := by
        rw [hfinish, hm]
        simp [Nat.not_le_of_gt hlt]
      rw [← hm]
      exact signed_continue x value1 bytes a idx index1 b i3 hidx hnext hn hbytes hb hsmall
        i3_post a_post index1_post
    · have h0 : value1 ≠ 0#i32 := by assumption
      have hm : value1 ≠ (-1)#i32 := by assumption
      have hn : ¬SignedFits x.val idx.val := by simp [hfinish, h0, hm]
      exact signed_continue x value1 bytes a idx index1 b i3 hidx hnext hn hbytes hb hsmall
        i3_post a_post index1_post
  · refine ⟨by scalar_tac, by simp, by simp, ?_⟩
    intro i hi
    simpa using byteAt_repeat i hi

theorem encode_s32_spec (x : I32) :
    ∃ bytes k, encode_s32 x = ok (some (bytes, k)) ∧ SignedCanonicalEncoding x.val bytes k.val := by
  have hbits : encode_s32.BITS = core.num.I32.BITS := by rw [encode_s32.BITS]; rfl
  obtain ⟨⟨bytes, idx, b⟩, hout, hpost⟩ := total_result (encode_signed_loop_spec x)
  obtain ⟨hidx, hfit, hprevious, hb, hbytes⟩ := hpost
  dsimp at *
  have hwp : WP.spec (encode_s32 x)
      (fun result => ∃ bytes k, result = some (bytes, k) ∧ SignedCanonicalEncoding x.val bytes k.val) := by
    unfold encode_s32
    simp [hbits, hout]
    step*
    refine ⟨output2, i, rfl, ?_⟩
    rw [output2_post, i_post]
    refine ⟨by omega, by omega, by simpa using hfit, ?_, ?_⟩
    · intro hk
      have hi : idx.val + 1 - 2 = idx.val - 1 := by omega
      rw [hi]
      exact hprevious (by omega)
    · intro j hj
      rw [byteAt_set _ _ _ _ hj, hbytes _ hj]
      by_cases hji : j = idx.val
      · simp [hji, hb]
      · by_cases hlt : j < idx.val
        · have hlt' : j < idx.val + 1 := by omega
          have hmore : j + 1 < idx.val + 1 := by omega
          simp [hji, hlt, hlt', hmore]
        · have hnlt : ¬j < idx.val + 1 := by omega
          simp [hji, hlt, hnlt]
  obtain ⟨value, heq, bytes, k, hsome, hspec⟩ := total_result hwp
  exact ⟨bytes, k, heq.trans (congrArg Result.ok hsome), hspec⟩


def SignedFixedEncoding (x : Int) (bytes : Bytes32) : Prop :=
  ∀ i, i < 5 → byteAt bytes i = signedByte x i (decide (i + 1 < 5))

private def ExtensionState (x : I32) (negative : Bool) (bytes : Bytes32) (index : Usize) : Prop :=
  0 < index.val ∧ index.val ≤ 5 ∧
  x.val / 128 ^ index.val = (if negative then -1 else 0) ∧
  ∀ i, i < index.val → byteAt bytes i = signedByte x.val i true

private theorem append_signed_byte {x : Int} {bytes out : Bytes32} {index next : Usize} {byte : U8}
    (hi : index.val < 5) (hn : next.val = index.val + 1)
    (hbyte : byte.val = signedByte x index.val true) (hout : out = bytes.set index byte)
    (hprefix : ∀ i, i < index.val → byteAt bytes i = signedByte x i true) :
    ∀ j, j < next.val → byteAt out j = signedByte x j true := by
  intro j hj
  rw [hout, byteAt_set _ _ _ _ (by omega)]
  by_cases he : j = index.val
  · simp [he, hbyte]
  · simp [he, hprefix j (by omega)]

private theorem fixed_initial_spec (x : I32) :
    WP.spec (encode_fixed_s32_loop4 x (Array.repeat 5#usize 0#u8) 0#usize)
      (fun (index, neg, bytes) => ExtensionState x neg bytes index) := by
  unfold encode_fixed_s32_loop4
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.2.val)
    (inv := SignedEncodingInvariant x)
  · rintro ⟨value, bytes, idx⟩ ⟨hidx, hvalue, hprevious, hbytes⟩
    dsimp at *
    unfold encode_fixed_s32_loop4.body
    step*
    all_goals
      have hd := signed_digit value i b i_post1 b_post
      have hsmall : b.val < 128 := by omega
      have hq : value1.val = value.val / 128 := by
        rw [value1_post, Int.shiftRight_eq_div_pow]
        rfl
      have hnext : value1.val = x.val / 128 ^ (idx.val + 1) := by
        rw [hq, hvalue, Int.ediv_ediv_of_nonneg (by positivity), pow_succ]
      have hfinish : SignedFits x.val idx.val ↔
          (value1 = 0#i32 ∧ b.val < 64) ∨ (value1 = (-1)#i32 ∧ 64 ≤ b.val) := by
        unfold SignedFits
        rw [← hvalue, fits_iff_step, ← hq, ← hd]
        have hz : value1.val = 0 ↔ value1 = 0#i32 :=
          ⟨fun h => int_scalar_eq_of_val h, fun h => congrArg IScalar.val h⟩
        have hn : value1.val = -1 ↔ value1 = (-1)#i32 :=
          ⟨fun h => int_scalar_eq_of_val h, fun h => congrArg IScalar.val h⟩
        rw [hz, hn]
      have hb : b.val = signedByte x.val idx.val false := by
        rw [hd, hvalue]
        simp [signedByte]

      have hcont : i1.val = signedByte x.val idx.val true := by
        rw [i1_post, UScalar.val_or]
        change b.val ||| 128 = _
        rw [set_continuation hsmall, hb]
        simp [signedByte]
      have hend (neg : Bool) (hrest : value1.val = (if neg then -1 else 0)) :
          ExtensionState x neg (index_mut_back i1) index1 := by
        refine ⟨by omega, by omega, ?_, ?_⟩
        · rwa [index1_post, ← hnext]
        · apply append_signed_byte hidx index1_post hcont
          · rw [index_mut_back_post]
          · intro j hj
            simpa [hj] using hbytes j (by omega)
    · apply hend
      have he : value1 = 0#i32 := by assumption
      rw [he]
      rfl
    · have h0 : value1 = 0#i32 := by assumption
      have hsign : i2 ≠ 0#u8 := by assumption
      have hn : ¬SignedFits x.val idx.val := by
        have hnl : ¬b.val < 64 := fun h => hsign ((mask_sign b i2 i2_post hsmall).mpr h)
        rw [hfinish, h0]
        simp
        omega
      rw [← h0]
      exact signed_continue x value1 bytes _ idx index1 b i1 hidx hnext hn hbytes hb hsmall
        i1_post (by rw [index_mut_back_post]) index1_post
    · apply hend
      have he : value1 = (-1)#i32 := by assumption
      rw [he]
      rfl
    · have hm : value1 = (-1)#i32 := by assumption
      have hsign : ¬(i3 != 0#u8) = true := by assumption
      have hsign' : i3 = 0#u8 := by
        apply scalar_eq_of_val
        simpa using hsign
      have hlt := (mask_sign b i3 i3_post hsmall).mp hsign'
      have hn : ¬SignedFits x.val idx.val := by
        rw [hfinish, hm]
        simp [Nat.not_le_of_gt hlt]
      rw [← hm]
      exact signed_continue x value1 bytes _ idx index1 b i1 hidx hnext hn hbytes hb hsmall
        i1_post (by rw [index_mut_back_post]) index1_post
    · have h0 : value1 ≠ 0#i32 := by assumption
      have hm : value1 ≠ (-1)#i32 := by assumption
      have hn : ¬SignedFits x.val idx.val := by simp [hfinish, h0, hm]
      exact signed_continue x value1 bytes _ idx index1 b i1 hidx hnext hn hbytes hb hsmall
        i1_post (by rw [index_mut_back_post]) index1_post
  · refine ⟨by scalar_tac, by simp, by simp, ?_⟩
    intro i hi
    simpa using byteAt_repeat i hi

private theorem fixed_extend_spec (x : I32) (bytes : Bytes32) (idx : Usize) (neg : Bool)
    (hin : ExtensionState x neg bytes idx) :
    WP.spec (encode_fixed_s32_loop5 bytes idx neg)
      (fun (bytes, idx) => idx.val = 5 ∧
        ∀ j, j < 5 → byteAt bytes j = signedByte x.val j true) := by
  unfold encode_fixed_s32_loop5
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.val)
    (inv := fun (bytes, idx) => ExtensionState x neg bytes idx)
  · rintro ⟨bytes, idx⟩ ⟨hpos, hidx, hquot, hprefix⟩
    dsimp at *
    unfold encode_fixed_s32_loop5.body
    cases neg <;> simp <;> step*
    all_goals
      have hne : idx ≠ s.len := by assumption
      have hn : idx.val < 5 := by scalar_tac
      simp at hquot
      have hq : x.val / 128 ^ index1.val = (x.val / 128 ^ idx.val) / 128 := by
        rw [index1_post, Int.ediv_ediv_of_nonneg (by positivity), pow_succ]
      refine ⟨⟨by omega, by omega, ?_, ?_⟩, by omega⟩
      · rw [hq, hquot]
        decide
      · exact append_signed_byte hn index1_post (by simp [signedByte, hquot]) output1_post hprefix
  · exact hin

theorem encode_fixed_s32_spec (x : I32) :
    ∃ bytes, encode_fixed_s32 x = ok (some bytes) ∧ SignedFixedEncoding x.val bytes := by
  have hbits : encode_fixed_s32.BITS = core.num.I32.BITS := by rw [encode_fixed_s32.BITS]; rfl
  obtain ⟨⟨idx, neg, bytes⟩, hfirst, hstart⟩ := total_result (fixed_initial_spec x)
  obtain ⟨⟨buffer, count⟩, hsecond, hcount, hdigits⟩ :=
    total_result (fixed_extend_spec x bytes idx neg hstart)
  have hwp : WP.spec (encode_fixed_s32 x)
      (fun result => ∃ bytes, result = some bytes ∧ SignedFixedEncoding x.val bytes) := by
    unfold encode_fixed_s32
    simp [hbits, hfirst, hsecond]
    step*
    refine ⟨output2, rfl, ?_⟩
    intro j hj
    rw [output2_post, byteAt_set _ _ _ _ hj]
    have hi : i.val = 4 := by omega
    by_cases hji : j = i.val
    · simp only [hji, ite_true]
      have hread : i1.val = byteAt buffer i.val := by
        rw [i1_post]
        simp [byteAt, List.getElem?_eq_getElem (by scalar_tac : i.val < buffer.val.length)]
      have hmod : i2.val = i1.val % 128 := by simpa [mask_payload] using i2_post
      rw [hmod, hread, hdigits _ (by omega)]
      have hsmall : (x.val / 128 ^ i.val % 128).toNat < 128 := by omega
      simp [signedByte, hi] at *
      omega
    · have hmore : j + 1 < 5 := by omega
      simp [hji, hmore, hdigits _ hj]
  obtain ⟨value, heq, bytes, hsome, hspec⟩ := total_result hwp
  exact ⟨bytes, heq.trans (congrArg Result.ok hsome), hspec⟩

def signedSum (sum byte index : Nat) : Int :=
  let raw := sum + byte % 128 * 128 ^ index
  if 64 ≤ byte then (raw : Int) - (128 ^ (index + 1) : Nat) else raw

def decodeSignedDigits (bytes : Bytes32) (sum index : Nat) : Nat → Option (Int × Nat)
  | 0 => none
  | remaining + 1 =>
    let byte := byteAt bytes index
    if byte < 128 then
      let value := signedSum sum byte index
      if -2^31 ≤ value ∧ value < 2^31 then some (value, index + 1) else none
    else decodeSignedDigits bytes (sum + byte % 128 * 128 ^ index) (index + 1) remaining

def decodeSignedMeaning (bytes : Bytes32) : Option (Int × Nat) :=
  decodeSignedDigits bytes 0 0 5

def decodeSignedValue (out : Option (I32 × Usize)) : Option (Int × Nat) :=
  out.map fun (value, count) => (value.val, count.val)

private def DecodeSignedInvariant (bytes : Bytes32) (state : I32 × U32 × Usize) : Prop :=
  state.2.2.val < 5 ∧ state.2.1.val = 7 * state.2.2.val ∧
  state.1.bv.toNat < 128 ^ state.2.2.val ∧
  decodeSignedDigits bytes state.1.bv.toNat state.2.2.val (5 - state.2.2.val) =
    decodeSignedMeaning bytes

private theorem decode_unroll (bytes : Bytes32) (sum index : Nat) (hi : index < 5) :
    decodeSignedDigits bytes sum index (5 - index) =
      if byteAt bytes index < 128 then
        let value := signedSum sum (byteAt bytes index) index
        if -2^31 ≤ value ∧ value < 2^31 then some (value, index + 1) else none
      else decodeSignedDigits bytes (sum + (byteAt bytes index % 128) * 128 ^ index)
          (index + 1) (5 - (index + 1)) := by
  have hfuel : 5 - index = (5 - (index + 1)) + 1 := by omega
  rw [hfuel]
  rfl

private theorem continuation_iff (byte flag : U8) (h : flag.val = (byte &&& 128#u8).val) :
    (flag != 0#u8) = true ↔ ¬byte.val < 128 := by
  have hbyte : byte.val < 256 := by scalar_tac
  have hdiv := @Nat.and_div_two_pow byte.val 128 7
  have hmod := @Nat.and_mod_two_pow byte.val 128 7
  change (byte.val &&& 128) / 128 = (byte.val / 128) &&& 1 at hdiv
  change (byte.val &&& 128) % 128 = (byte.val % 128) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  have hf : flag.val = byte.val &&& 128 := by simpa using h
  simp
  omega

private theorem unsigned_byte_bits (byte : U8) :
    (UScalar.hcast .I32 byte).bv.toNat = byte.val := by
  rw [UScalar.hcast_bv_eq, BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  scalar_tac

private theorem earlier_in_range {sum byte idx : Nat} (ha : sum < 128^idx)
    (_hb : byte < 128) (hi : idx + 1 < 5) :
    -2^31 ≤ signedSum sum byte idx ∧ signedSum sum byte idx < 2^31 := by
  have hsize : 128^(idx+1) ≤ 128^4 := Nat.pow_le_pow_right (by decide) (by omega)
  have hsum := decode_append ha (Nat.mod_lt byte (by decide : 0<128))
  change 128^(idx+1) ≤ 268435456 at hsize
  simp only [signedSum]
  split <;> omega

private theorem final_in_range {sum byte : Nat} (ha : sum < 128^4) (hb : byte < 128) :
    (-2^31 ≤ signedSum sum byte 4 ∧ signedSum sum byte 4 < 2^31) ↔
      byte < 8 ∨ 120 ≤ byte := by
  have hm : byte % 128 = byte := Nat.mod_eq_of_lt hb
  change sum < 268435456 at ha
  unfold signedSum
  rw [hm]
  change (-2147483648 ≤ (if 64 ≤ byte then (↑(sum + byte * 268435456) : Int) - 34359738368
              else ↑(sum + byte * 268435456)) ∧
          (if 64 ≤ byte then (↑(sum + byte * 268435456) : Int) - 34359738368
              else ↑(sum + byte * 268435456)) < 2147483648) ↔ _
  by_cases hn : 64 ≤ byte <;> simp only [hn, ite_true, ite_false] <;> omega

private theorem final_mask_zero {n : U8} (h : n.val < 128) :
    (n &&& 120#u8) = 0#u8 ↔ n.val < 8 := by
  have hd := @Nat.and_div_two_pow n.val 120 3
  have hm := @Nat.and_mod_two_pow n.val 120 3
  change (n.val &&& 120) / 8 = (n.val / 8) &&& 15 at hd
  change (n.val &&& 120) % 8 = (n.val % 8) &&& 0 at hm
  have hh : (n.val / 8) &&& 15 = n.val / 8 :=
    Nat.and_two_pow_sub_one_of_lt_two_pow (n := 4) (by omega)
  rw [hh] at hd
  simp at hm
  constructor
  · intro he
    have hz : n.val &&& 120 = 0 := by simpa using congrArg UScalar.val he
    omega
  · intro hl
    apply scalar_eq_of_val
    change n.val &&& 120 = 0
    omega

private theorem decode_signed_loop_spec (bytes : Bytes32) :
    WP.spec (decode_s32_loop bytes 0#i32 0#u32 0#usize)
      (fun out => decodeSignedValue out = decodeSignedMeaning bytes) := by
  unfold decode_s32_loop
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.2.val)
    (inv := DecodeSignedInvariant bytes)
  · rintro ⟨acc, shift, idx⟩ ⟨hidx, hshift, hacc, hspec⟩
    dsimp at *
    unfold decode_s32_loop.body
    rw [decode_s32.BITS]
    step*
    all_goals
      have hbyte : byteAt bytes idx.val = n.val := by
        rw [n_post]
        simp [byteAt, List.getElem?_eq_getElem (by scalar_tac : idx.val < bytes.val.length)]
      have hlast : i2.val = 28 := by omega
      have hflag := continuation_iff n i i_post
      rw [decode_unroll _ _ _ hidx, hbyte] at hspec
    · have he : shift = i2 := by assumption
      have hfinal : idx.val = 4 := by
        have hv := congrArg UScalar.val he
        omega
      have hremainder : i1 = 4#u32 := scalar_eq_of_val (by scalar_tac)
      have hsat : core.num.U32.saturating_sub 4#u32 1#u32 = 3#u32 := by rfl
      have hmask : IScalar.hcast .U8 ((-8)#i8 &&& 127#i8) = 120#u8 := by rfl
      rw [hremainder]
      simp only [lift, hsat]
      step*
      all_goals
        have hi4 : i4 = (-8)#i8 := by
          apply int_scalar_eq_of_val
          rw [i4_post, I8.size, I8.numBits]
          decide
        have hm : IScalar.hcast .U8 (i4 &&& 127#i8) = 120#u8 := by rw [hi4, hmask]
      · have hcontinue : (i != 0#u8) = true := by assumption
        have hnonterminal := hflag.mp hcontinue
        simp [decodeSignedValue, ← hspec, hnonterminal, hfinal, decodeSignedDigits]
      · have hcontinue : ¬(i != 0#u8) = true := by assumption
        have hterminal := Classical.byContradiction fun ht => hcontinue (hflag.mpr ht)
        have hbad : (n &&& IScalar.hcast .U8 (i4 &&& 127#i8) != 0#u8) = true := by assumption
        rw [hm] at hbad
        have hgt : ¬n.val < 8 := by
          intro hh
          have he := (final_mask_zero hterminal).mpr hh
          simp [he] at hbad
        have hlow : n < IScalar.hcast .U8 (i4 &&& 127#i8) := by assumption
        rw [hm] at hlow
        have hlt : n.val < 120 := hlow
        have hrange : ¬(-2^31 ≤ signedSum acc.bv.toNat n.val idx.val ∧
            signedSum acc.bv.toNat n.val idx.val < 2^31) := by
          rw [hfinal] at hacc ⊢
          rw [final_in_range hacc hterminal]
          omega
        simp only [decodeSignedValue, Option.map_none, ← hspec, hterminal, ite_true,
          hrange, ite_false]
      all_goals
        have hcontinue : ¬(i != 0#u8) = true := by assumption
        have hterminal : n.val < 128 := Classical.byContradiction fun ht => hcontinue (hflag.mpr ht)
        have hbound : n.val < 8 ∨ 120 ≤ n.val := by
          first
          | have hhigh : ¬n < IScalar.hcast .U8 (i4 &&& 127#i8) := by assumption
            rw [hm] at hhigh
            right
            exact Nat.le_of_not_gt (show ¬n.val < 120 from hhigh)
          | have hz : ¬(n &&& IScalar.hcast .U8 (i4 &&& 127#i8) != 0#u8) = true := by assumption
            rw [hm] at hz
            have heq : (n &&& 120#u8) = 0#u8 := by
              apply scalar_eq_of_val
              simpa using hz
            exact Or.inl ((final_mask_zero hterminal).mp heq)
        have hrange : -2^31 ≤ signedSum acc.bv.toNat n.val idx.val ∧
            signedSum acc.bv.toNat n.val idx.val < 2^31 := by
          rw [hfinal] at hacc ⊢
          exact (final_in_range hacc hterminal).mpr hbound
        have hshift' : i2.val = 7*idx.val := by omega
        have hbits : (acc ||| i9).bv =
            BitVec.ofNat 32 (acc.bv.toNat + n.val % 128 * 128^idx.val) := by
          change (acc.bv ||| i9.bv) = _
          simp only [I32.bv] at i9_post1 ⊢
          rw [i9_post1, hshift', bv_or_chunk _ _ (by rwa [pow_radix]), pow_radix]
          simp [mask_payload]
        have hwrap : (acc ||| i9).bv = BitVec.ofInt 32 (signedSum acc.bv.toNat n.val idx.val) := by
          rw [hbits]
          unfold signedSum
          split
          · apply bv_sign_wrap
            omega
          · rfl
        have hv : (acc ||| i9).val = signedSum acc.bv.toNat n.val idx.val := by
          simp only [IScalar.val, I32.bv] at hwrap ⊢
          rw [hwrap]
          exact BitVec.toInt_ofInt_eq_self (by decide) hrange.1 hrange.2
        simp only [decodeSignedValue, Option.map_some, hv, pos1_post, ← hspec,
          hterminal, hrange, ite_true, and_self]
    all_goals
      have he : shift ≠ i2 := by assumption
      have hshort : idx.val + 1 < 5 := by
        by_contra! h
        exact he (scalar_eq_of_val (by omega))
      have hbits : result1.bv =
          BitVec.ofNat 32 (acc.bv.toNat + n.val % 128 * 128^idx.val) := by
        simp only [I32.bv] at result1_post1 i9_post1 ⊢
        rw [result1_post1, i9_post1, hshift, bv_or_chunk _ _ (by rwa [pow_radix]), pow_radix,
          i8_post, unsigned_byte_bits]
        simp [i7_post, mask_payload]
      have hsum := decode_append hacc (Nat.mod_lt n.val (by decide : 0 < 128))
      have hmax : 128^(idx.val+1) ≤ 128^4 := Nat.pow_le_pow_right (by decide) (by omega)
      have hraw : result1.bv.toNat = acc.bv.toNat + n.val % 128 * 128^idx.val := by
        rw [hbits, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (lt_of_lt_of_le hsum (le_trans hmax (by decide)))
    · have hcontinue : (i != 0#u8) = true := by assumption
      have hn := hflag.mp hcontinue
      simp only [DecodeSignedInvariant, shift1_post, pos1_post, hraw, ite_eq_right hn] at *
      exact ⟨⟨hshort, by omega, hsum, hspec⟩, by omega⟩
    · have hcontinue : ¬(i != 0#u8) = true := by assumption
      have hterminal : n.val < 128 := Classical.byContradiction fun ht => hcontinue (hflag.mpr ht)
      have hsign : (i10 != 0#u8) = true := by assumption
      have hn : 64 ≤ n.val := by
        apply Nat.le_of_not_gt
        intro hh
        have hzero := (mask_sign n i10 i10_post hterminal).mpr hh
        simp [hzero] at hsign
      have hrange := earlier_in_range hacc hterminal hshort
      have hshift' : shift1.val = 7*(idx.val+1) := by omega
      have heq : result2.bv = BitVec.ofInt 32 (signedSum acc.bv.toNat n.val idx.val) := by
        simp only [I32.bv] at result2_post1 i11_post1 ⊢
        rw [result2_post1, i11_post1]
        change (result1.bv ||| (BitVec.allOnes 32 <<< shift1.val)) = _
        rw [hshift', bv_sign_extend _ (by rwa [pow_radix, hraw]), pow_radix, hraw,
          signedSum, ite_eq_left hn]
      have hv : result2.val = signedSum acc.bv.toNat n.val idx.val := by
        simp only [IScalar.val, I32.bv] at heq ⊢
        rw [heq]
        exact BitVec.toInt_ofInt_eq_self (by decide) hrange.1 hrange.2
      simp only [decodeSignedValue, Option.map_some, hv, pos1_post, ← hspec,
        hterminal, hrange, ite_true, and_self]
    · have hcontinue : ¬(i != 0#u8) = true := by assumption
      have hterminal : n.val < 128 := Classical.byContradiction fun ht => hcontinue (hflag.mpr ht)
      have hsign : ¬(i10 != 0#u8) = true := by assumption
      have hzero : i10 = 0#u8 := by
        apply scalar_eq_of_val
        simpa using hsign
      have hn := (mask_sign n i10 i10_post hterminal).mp hzero
      have hrange := earlier_in_range hacc hterminal hshort
      have heq : result1.bv = BitVec.ofInt 32 (signedSum acc.bv.toNat n.val idx.val) := by
        rw [hbits, signedSum, ite_eq_right (Nat.not_le_of_gt hn)]
        rfl
      have hv : result1.val = signedSum acc.bv.toNat n.val idx.val := by
        simp only [IScalar.val, I32.bv] at heq ⊢
        rw [heq]
        exact BitVec.toInt_ofInt_eq_self (by decide) hrange.1 hrange.2
      simp only [decodeSignedValue, Option.map_some, hv, pos1_post, ← hspec,
        hterminal, hrange, ite_true, and_self]
  · refine ⟨by scalar_tac, by decide, by decide, rfl⟩

theorem decode_s32_spec (bytes : Bytes32) :
    ∃ out, decode_s32 bytes = ok out ∧ decodeSignedValue out = decodeSignedMeaning bytes := by
  have hbits : core.num.I32.BITS = decode_s32.BITS := by rw [decode_s32.BITS]; rfl
  unfold decode_s32
  simp only [hbits, lt_self_iff_false, ↓reduceIte]
  exact total_result (decode_signed_loop_spec bytes)

end leb128fmt.signed32
