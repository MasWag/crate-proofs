import LebCore

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow

namespace leb128fmt

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

private theorem mask_continuation (b : U8) : (b.val &&& 128) = 0 ↔ b.val < 128 := by
  have hb : b.val < 256 := by scalar_tac
  have hdiv := @Nat.and_div_two_pow b.val 128 7
  have hmod := @Nat.and_mod_two_pow b.val 128 7
  change (b.val &&& 128) / 128 = (b.val / 128) &&& 1 at hdiv
  change (b.val &&& 128) % 128 = (b.val % 128) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  omega

theorem is_last_spec (b : U8) :
    is_last b = ok (decide (b.val < 128)) := by
  unfold is_last
  simp only [lift]
  have h : (b &&& 128#u8) = 0#u8 ↔ b.val < 128 := by
    have hval : (b &&& 128#u8).val = 0#u8.val ↔ b.val < 128 := by
      simpa using mask_continuation b
    exact ⟨fun h => hval.mp (congrArg UScalar.val h), fun h => scalar_eq_of_val (hval.mpr h)⟩
  simp [h]

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

def CanonicalEncoding (x : Nat) (bytes : Bytes32) (k : Nat) : Prop :=
  0 < k ∧ k ≤ 5 ∧ x < 128 ^ k ∧ (1 < k → 128 ^ (k - 1) ≤ x) ∧
  ∀ i, i < 5 →
    byteAt bytes i = if i < k then encodedByte x i (decide (i + 1 < k)) else 0

private def EncodingInvariant (x : U32) (state : U32 × Bytes32 × Usize) : Prop :=
  state.2.2.val < 5 ∧
  state.1.val = x.val / 128 ^ state.2.2.val ∧
  (0 < state.2.2.val → 128 ^ state.2.2.val ≤ x.val) ∧
  ∀ i, i < 5 → byteAt state.2.1 i =
    if i < state.2.2.val then encodedByte x.val i true else 0

private theorem div_radix_succ (x i : Nat) :
    (x / 128 ^ i) / 128 = x / 128 ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

private theorem pow_mono {i j : Nat} (h : i ≤ j) : 128 ^ i ≤ 128 ^ j :=
  Nat.pow_le_pow_right (by decide) h

private theorem encode_loop_spec (x : U32) :
    WP.spec (encode_u32_loop1 x (Array.repeat 5#usize 0#u8) 0#usize)
      (fun (out, k) => CanonicalEncoding x.val out k.val) := by
  unfold encode_u32_loop1
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.2.val)
    (inv := EncodingInvariant x)
  · rintro ⟨value, bytes, idx⟩ ⟨hidx, hvalue, hpositive, hbytes⟩
    dsimp at *
    have hx : x.val < 2^32 := by scalar_tac
    unfold encode_u32_loop1.body
    step*
    all_goals
      have hmasked : i.val = payloadDigit x.val idx.val := by
        simpa [payloadDigit, mask_payload, hvalue] using i_post
      have hb : b.val = payloadDigit x.val idx.val := by
        rw [b_post, UScalar.cast_val_eq, hmasked]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 128)) (by decide)
      have hquot : value1.val = x.val / 128 ^ (idx.val + 1) := by
        rw [value1_post, Nat.shiftRight_eq_div_pow, hvalue]
        exact div_radix_succ _ _
      rw [index_mut_back_post]
    · have hsmall : x.val < 128 ^ (idx.val + 1) := by
        have hz : value1 = 0#u32 := by assumption
        have he : x.val / 128 ^ (idx.val + 1) = 0 := by rw [← hquot, hz]; rfl
        exact (Nat.div_eq_zero_iff.mp he).resolve_left (by positivity)
      rw [index1_post]
      refine ⟨by omega, by omega, hsmall, ?_, ?_⟩
      · intro hk
        rw [Nat.add_sub_cancel]
        exact hpositive (by omega)
      · intro j hj
        rw [byteAt_set _ _ _ _ hj, hbytes j hj]
        by_cases hji : j = idx.val
        · simp [hji, hb, encodedByte]
        · by_cases hlt : j < idx.val
          · have hlt' : j < idx.val + 1 := by omega
            have hmore : j + 1 < idx.val + 1 := by omega
            simp [hji, hlt, hlt', hmore]
          · have hnlt : ¬j < idx.val + 1 := by omega
            simp [hji, hlt, hnlt]
    · have hlarge : 128 ^ (idx.val + 1) ≤ x.val := by
        apply Nat.le_of_not_gt
        intro h
        have hv : value1.val = 0 := hquot.trans (Nat.div_eq_of_lt h)
        have hnz : value1 ≠ 0#u32 := by assumption
        exact hnz (scalar_eq_of_val hv)
      have hnext : idx.val + 1 < 5 := by
        by_contra! h
        have := le_trans (pow_mono h) hlarge
        omega
      have hb1 : b1.val = encodedByte x.val idx.val true := by
        rw [b1_post, UScalar.val_or]
        change b.val ||| 128 = _
        rw [set_continuation (hb ▸ Nat.mod_lt _ (by decide)), hb]
        rfl
      simp only [EncodingInvariant, index1_post]
      refine ⟨⟨hnext, hquot, fun _ => hlarge, ?_⟩, by omega⟩
      · intro j hj
        rw [byteAt_set _ _ _ _ hj, hbytes j hj]
        by_cases hji : j = idx.val
        · simp [hji, hb1]
        · have hlt : j < idx.val + 1 ↔ j < idx.val := by omega
          simp [hji, hlt]
  · refine ⟨by scalar_tac, by simp, by simp, ?_⟩
    intro i hi
    simpa using byteAt_repeat i hi

theorem encode_u32_spec (x : U32) :
    ∃ bytes k, encode_u32 x = ok (some (bytes, k)) ∧ CanonicalEncoding x.val bytes k.val := by
  obtain ⟨⟨bytes, k⟩, hout, hpost⟩ := total_result (encode_loop_spec x)
  refine ⟨bytes, k, ?_, hpost⟩
  unfold encode_u32
  have hbits : core.num.U32.BITS = encode_u32.BITS := by rw [encode_u32.BITS]; rfl
  simp [hbits, hout]

def FixedEncoding (x : Nat) (bytes : Bytes32) : Prop :=
  ∀ i, i < 5 → byteAt bytes i = encodedByte x i (decide (i + 1 < 5))

private def FixedInvariant (x : U32) (state : Bytes32 × Usize × U32) : Prop :=
  state.2.1.val < 5 ∧ state.2.2.val = 7 * state.2.1.val ∧
  ∀ i, i < state.2.1.val → byteAt state.1 i = encodedByte x.val i true

private theorem pow_radix (i : Nat) : 2 ^ (7 * i) = 128 ^ i := by
  rw [Nat.pow_mul]

private theorem encode_fixed_loop_spec (x : U32) :
    WP.spec (encode_fixed_u32_loop1 x (Array.repeat 5#usize 0#u8) 0#usize 0#u32)
      (FixedEncoding x.val) := by
  unfold encode_fixed_u32_loop1
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.1.val)
    (inv := FixedInvariant x)
  · rintro ⟨bytes, idx, shift⟩ ⟨hidx, hshift, hbytes⟩
    dsimp at *
    unfold encode_fixed_u32_loop1.body
    rw [encode_fixed_u32.BITS]
    step*
    all_goals
      have hv : v.val = x.val / 128 ^ idx.val := by
        rw [v_post, Nat.shiftRight_eq_div_pow, hshift, pow_radix]
      have hmasked : i.val = payloadDigit x.val idx.val := by
        simpa [payloadDigit, mask_payload, hv] using i_post
      have hb : b.val = payloadDigit x.val idx.val := by
        rw [b_post, UScalar.cast_val_eq, hmasked]
        apply Nat.mod_eq_of_lt
        exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 128)) (by decide)
      have hlast : i2.val = 28 := by omega
      rw [index_mut_back_post]
    · have heq : shift = i2 := by assumption
      have hfinal : idx.val = 4 := by
        have he := congrArg UScalar.val heq
        omega
      intro j hj
      rw [byteAt_set _ _ _ _ (by omega)]
      by_cases hji : j = idx.val
      · simp [hji, hfinal, hb, encodedByte]
      · have hlt : j < idx.val := by omega
        have hmore : j + 1 < 5 := by omega
        simp [hji, hbytes j hlt, hmore]
    · have hne : shift ≠ i2 := by assumption
      have hnext : idx.val + 1 < 5 := by
        by_contra! h
        apply hne
        apply scalar_eq_of_val
        omega
      have hb1 : b1.val = encodedByte x.val idx.val true := by
        rw [b1_post, UScalar.val_or]
        change b.val ||| 128 = _
        rw [set_continuation (hb ▸ Nat.mod_lt _ (by decide)), hb]
        rfl
      simp only [FixedInvariant, index1_post, shift1_post]
      refine ⟨⟨hnext, by omega, ?_⟩, by omega⟩
      intro j hj
      rw [byteAt_set _ _ _ _ (by omega)]
      by_cases hji : j = idx.val
      · simp [hji, hb1]
      · have hlt : j < idx.val := by omega
        simp [hji, hbytes j hlt]
  · refine ⟨by scalar_tac, by simp, ?_⟩
    intro i hi
    scalar_tac

theorem encode_fixed_u32_spec (x : U32) :
    ∃ bytes, encode_fixed_u32 x = ok (some bytes) ∧ FixedEncoding x.val bytes := by
  obtain ⟨bytes, hout, hpost⟩ := total_result (encode_fixed_loop_spec x)
  refine ⟨bytes, ?_, hpost⟩
  unfold encode_fixed_u32
  have hbits : core.num.U32.BITS = encode_fixed_u32.BITS := by rw [encode_fixed_u32.BITS]; rfl
  simp [hbits, hout]

/-- Interpret little-endian base-128 digits up to the first byte below 128.
    The zero-fuel case represents an input with no terminator. -/
def decodeDigits (bytes : Bytes32) (value i : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    let byte := byteAt bytes i
    let next := value + (byte % 128) * 128 ^ i
    if byte < 128 then
      if next < 2 ^ 32 then some (next, i + 1) else none
    else decodeDigits bytes next (i + 1) fuel

def decodeMeaning (bytes : Bytes32) : Option (Nat × Nat) :=
  decodeDigits bytes 0 0 5

def decodeValue (out : Option (U32 × Usize)) : Option (Nat × Nat) :=
  out.map fun (value, count) => (value.val, count.val)

private def DecodeInvariant (bytes : Bytes32) (state : U32 × U32 × Usize) : Prop :=
  0 < state.2.2.val ∧ state.2.2.val < 5 ∧
  state.2.1.val = 7 * state.2.2.val ∧ state.1.val < 128 ^ state.2.2.val ∧
  decodeDigits bytes state.1.val state.2.2.val (5 - state.2.2.val) = decodeMeaning bytes

private theorem byteAt_index (bytes : Bytes32) (i : Nat) (hi : i < bytes.val.length) :
    byteAt bytes i = bytes.val[i].val := by
  simp [byteAt, List.getElem?_eq_getElem hi]

private theorem mask_continuation_val (b flag : U8) (h : flag.val = (b &&& 128#u8).val) :
    flag = 0#u8 ↔ b.val < 128 := by
  have hval : flag.val = 0#u8.val ↔ b.val < 128 := by
    rw [h]
    simpa using mask_continuation b
  exact ⟨fun he => hval.mp (congrArg UScalar.val he),
    fun hh => scalar_eq_of_val (hval.mpr hh)⟩

private theorem decode_unroll (bytes : Bytes32) (value i : Nat) (hi : i < 5) :
    decodeDigits bytes value i (5 - i) =
      if byteAt bytes i < 128 then
        if value + byteAt bytes i % 128 * 128 ^ i < 2 ^ 32 then
          some (value + byteAt bytes i % 128 * 128 ^ i, i + 1)
        else none
      else decodeDigits bytes (value + byteAt bytes i % 128 * 128 ^ i) (i + 1) (5 - (i + 1)) := by
  have hfuel : 5 - i = (5 - (i + 1)) + 1 := by omega
  rw [hfuel]
  rfl

private theorem decode_append {acc digit index : Nat} (ha : acc < 128 ^ index)
    (hd : digit < 128) : acc + digit * 128 ^ index < 128 ^ (index + 1) := by
  rw [Nat.pow_succ]
  have hp : 0 < 128 ^ index := by positivity
  nlinarith

private theorem decode_or {index : Nat} {acc digit shifted result : U32}
    (ha : acc.val < 128 ^ index)
    (hbound : digit.val * 128 ^ index < 2 ^ 32)
    (hshift : shifted.val = (digit.val <<< (7 * index)) % U32.size)
    (hor : result.val = (acc ||| shifted).val) :
    result.val = acc.val + digit.val * 128 ^ index := by
  have hv : shifted.val = digit.val * 128 ^ index := by
    rw [hshift, Nat.shiftLeft_eq, pow_radix]
    rw [U32.size, U32.numBits]
    exact Nat.mod_eq_of_lt hbound
  rw [hor, UScalar.val_or, hv, Nat.or_comm, ← pow_radix]
  rw [Nat.mul_comm digit.val, ← Nat.two_pow_add_eq_or_of_lt (by rwa [pow_radix]) digit.val,
    Nat.add_comm acc.val]

private theorem decode_loop_spec (bytes : Bytes32) (value : U32) (shift : U32) (pos : Usize)
    (hinit : DecodeInvariant bytes (value, shift, pos)) :
    WP.spec (decode_u32_loop bytes value shift pos) (fun out => decodeValue out = decodeMeaning bytes) := by
  unfold decode_u32_loop
  apply loop.spec_decr_nat (measure := fun state => 5 - state.2.2.val)
    (inv := DecodeInvariant bytes)
  · rintro ⟨acc, sh, idx⟩ ⟨hpos, hidx, hsh, hacc, hspec⟩
    dsimp at *
    unfold decode_u32_loop.body
    rw [decode_u32.BITS]
    step*
    all_goals
      have hlen : bytes.val.length = 5 := by have := bytes.property; scalar_tac
      have hbyte : byteAt bytes idx.val = n.val := by
        rw [n_post]
        exact byteAt_index _ _ (by omega)
      have hlast : i1.val = 28 := by omega
      rw [decode_unroll _ _ _ hidx, hbyte] at hspec
    · have hs : sh = i1 := by assumption
      have hfinal : idx.val = 4 := by
        have he := congrArg UScalar.val hs
        omega
      have hlimit : i2.val = 16 := by
        rw [i2_post, show i.val = 4 by omega]
        rw [U8.size, U8.numBits]
        decide
      have hlarge : 16 ≤ n.val := by scalar_tac
      rw [← hspec]
      by_cases ht : n.val < 128
      · rw [ite_eq_left ht, Nat.mod_eq_of_lt ht, hfinal, ite_eq_right]
        · rfl
        · change ¬(acc.val + n.val * 268435456 < 4294967296)
          omega
      · simp [ht, hfinal, decodeDigits, decodeValue]
    · have hs : sh = i1 := by assumption
      have hfinal : idx.val = 4 := by
        have he := congrArg UScalar.val hs
        omega
      have hlimit : i2.val = 16 := by
        rw [i2_post, show i.val = 4 by omega]
        rw [U8.size, U8.numBits]
        decide
      have hsmall : n.val < 16 := by scalar_tac
      have ht : n.val < 128 := by omega
      have hcast : i4.val = n.val := by simp [i4_post]
      have hb : i4.val * 128 ^ idx.val < 2 ^ 32 := by
        rw [hcast, hfinal]
        change n.val * 268435456 < 4294967296
        omega
      have hr := decode_or hacc hb (by rwa [← hsh, hs]) result1_post
      rw [hcast] at hr
      have hsum : acc.val + n.val * 128 ^ idx.val < 2 ^ 32 := by
        rw [hfinal] at hacc ⊢
        change acc.val < 268435456 at hacc
        change acc.val + n.val * 268435456 < 4294967296
        omega
      simp only [decodeValue, Option.map_some, hr, i6_post, ← hspec, ht, Nat.mod_eq_of_lt ht, hsum, ite_true]
    · have hlimit : i2.val = 16 := by
        rw [i2_post, show i.val = 4 by omega]
        rw [U8.size, U8.numBits]
        decide
      have hsmall : n.val < 16 := by scalar_tac
      have hn : i3 ≠ 0#u8 := by assumption
      exact False.elim (hn ((mask_continuation_val _ _ i3_post).mpr (by omega)))
    · have hs : sh ≠ i1 := by assumption
      have hnext : idx.val + 1 < 5 := by
        by_contra! h
        exact hs (scalar_eq_of_val (by omega))
      have hn : i3 = 0#u8 := by assumption
      have ht : n.val < 128 := (mask_continuation_val _ _ i3_post).mp hn
      have hcast : i4.val = n.val := by simp [i4_post]
      have hsum := decode_append hacc ht
      have hlarge : 128 ^ (idx.val + 1) ≤ 128 ^ 4 := pow_mono (by omega)
      have hbound : acc.val + n.val * 128 ^ idx.val < 2 ^ 32 :=
        lt_of_lt_of_le (lt_of_lt_of_le hsum hlarge) (by decide)
      have hb : i4.val * 128 ^ idx.val < 2 ^ 32 := by rw [hcast]; omega
      have hr := decode_or hacc hb (by rwa [← hsh]) result1_post
      rw [hcast] at hr
      simp only [decodeValue, Option.map_some, hr, i6_post, ← hspec, ht, Nat.mod_eq_of_lt ht, hbound, ite_true]
    · have hs : sh ≠ i1 := by assumption
      have hnext : idx.val + 1 < 5 := by
        by_contra! h
        exact hs (scalar_eq_of_val (by omega))
      have hn : i3 ≠ 0#u8 := by assumption
      have ht : ¬n.val < 128 := fun h => hn ((mask_continuation_val _ _ i3_post).mpr h)
      have hcast : i5.val = n.val % 128 := by simp [i5_post, i4_post, mask_payload]
      have hsum := decode_append hacc (Nat.mod_lt n.val (by decide : 0 < 128))
      have hlarge : 128 ^ (idx.val + 1) ≤ 128 ^ 4 := pow_mono (by omega)
      have hbound : acc.val + n.val % 128 * 128 ^ idx.val < 2 ^ 32 :=
        lt_of_lt_of_le (lt_of_lt_of_le hsum hlarge) (by decide)
      have hb : i5.val * 128 ^ idx.val < 2 ^ 32 := by rw [hcast]; omega
      have hr := decode_or hacc hb (by rwa [← hsh]) result1_post
      rw [hcast] at hr
      simp only [DecodeInvariant, pos1_post, shift1_post, hr, ite_eq_right ht] at *
      exact ⟨⟨by omega, hnext, by omega, hsum, hspec⟩, by omega⟩
  · exact hinit

theorem decode_u32_spec (bytes : Bytes32) :
    ∃ out, decode_u32 bytes = ok out ∧ decodeValue out = decodeMeaning bytes := by
  apply total_result
  unfold decode_u32
  have hbits : core.num.U32.BITS = decode_u32.BITS := by rw [decode_u32.BITS]; rfl
  simp only [hbits, lt_self_iff_false, ↓reduceIte]
  step*
  all_goals
    have hbyte : byteAt bytes 0 = n.val := by
      have hlen : bytes.val.length = 5 := by have := bytes.property; scalar_tac
      rw [n_post]
      exact byteAt_index _ _ (by omega)
  · have hi : i = 0#u8 := by assumption
    have ht : n.val < 128 := (mask_continuation_val _ _ i_post).mp hi
    have hv : i1.val = n.val := by simp [i1_post]
    have hbound : n.val < 2^32 := by omega
    simp only [decodeMeaning, decodeDigits, hbyte, ht, ite_true, Nat.pow_zero,
      Nat.mul_one, Nat.zero_add, Nat.mod_eq_of_lt ht, hbound, decodeValue,
      Option.map_some, hv]
    rfl
  · have hi : i ≠ 0#u8 := by assumption
    have ht : ¬n.val < 128 := fun h => hi ((mask_continuation_val _ _ i_post).mpr h)
    have hv : result.val = n.val % 128 := by simp [result_post, i1_post, mask_payload]
    apply decode_loop_spec
    refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, ?_, ?_⟩
    · rw [hv]
      exact Nat.mod_lt _ (by decide)
    · simp only [decodeMeaning, decodeDigits, hbyte, ite_eq_right ht, Nat.pow_zero,
        Nat.mul_one, Nat.zero_add, hv]
      rfl

theorem max_len_spec (bits : U32) :
    ∃ out, max_len bits = ok out ∧ out.val = (bits.val + 6) / 7 := by
  apply total_result
  unfold max_len
  step as ⟨remainder, hrem⟩
  by_cases hz : remainder = 0#u32
  · have hzero : bits.val % 7 = 0 := by rw [← hrem, hz]; rfl
    simp only [hz, ite_true]
    step*
  · have hnz : bits.val % 7 ≠ 0 := by
      intro he
      apply hz
      apply scalar_eq_of_val
      rw [hrem]
      exact he
    simp only [ite_eq_right hz]
    step*

end leb128fmt
