import ProofsUIntSliceEncode

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open leb128fmt_slice_probe

namespace leb128fmt.sliceProof

private abbrev Error := leb128fmt.Error
private abbrev needMore : Error := leb128fmt.InnerError.NeedMoreBytes
private abbrev invalid : Error := leb128fmt.InnerError.InvalidEncoding

/-- Accumulate the remaining base-128 digits. The final group must terminate
    and fit in the remaining field bits. Return the value and next cursor. -/
def unsignedDigits (bytes : Slice U8) (lastBits : Nat) :
    Nat → Nat → Nat → Nat → Except Error (Nat × Nat)
  | 0, pos, weight, value =>
    if bytes.val.length ≤ pos then .error needMore
    else
      let byte := byteAt bytes pos
      if byte < 2^lastBits then .ok (value + byte * weight, pos + 1)
      else .error invalid
  | fuel + 1, pos, weight, value =>
    if bytes.val.length ≤ pos then .error needMore
    else
      let byte := byteAt bytes pos
      let next := value + (byte % 128) * weight
      if byte < 128 then .ok (next, pos + 1)
      else unsignedDigits bytes lastBits fuel (pos + 1) (128 * weight) next

def UIntReaderPost {T : Type} (val : T → Nat) (start : Usize)
    (expected : Except Error (Nat × Nat))
    (out : core.result.Result T Error × Usize) : Prop :=
  match expected, out.1 with
  | .ok (x, p), .Ok actual => val actual = x ∧ out.2.val = p
  | .error x, .Err actual => actual = x ∧ out.2 = start
  | _, _ => False

structure UIntReaderOps (T : Type) where
  shl : leb128fmt_slice_probe.core.ops.bit.Shl T U32 T
  merge : leb128fmt_slice_probe.core.ops.bit.BitOrAssign T T
  byte : core.convert.From T U8
  width : leb128fmt_slice_probe.leb128fmt.UInt T

structure UIntReaderLaws {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) : Prop where
  size : ∃ w, ops.width.BITS = ok w ∧ w.val = storage
  append : ∀ (acc : T) (b : U8) (shift : U32),
    shift.val < storage → val acc < 2^shift.val →
    b.val * 2^shift.val < 2^storage →
    ∃ digit shifted out, ops.byte.«from» b = ok digit ∧
      ops.shl.shl digit shift = ok shifted ∧ ops.merge.bitor_assign acc shifted = ok out ∧
      val out = val acc + b.val * 2^shift.val
  fromByte : ∀ b : U8, ∃ x, ops.byte.«from» b = ok x ∧ val x = b.val

private theorem low_payload (b : U8) : (b &&& 127#u8).val = b.val % 128 := by
  rw [UScalar.val_and]
  exact Nat.and_two_pow_sub_one_eq_mod b.val 7

private theorem terminal_eq (b : U8) :
    leb128fmt.is_last b = ok (decide (b.val < 128)) := by
  have hb : b.val < 256 := by scalar_tac
  have hdiv := @Nat.and_div_two_pow b.val 128 7
  have hmod := @Nat.and_mod_two_pow b.val 128 7
  change (b.val &&& 128) / 128 = (b.val / 128) &&& 1 at hdiv
  change (b.val &&& 128) % 128 = (b.val % 128) &&& 0 at hmod
  rw [Nat.and_one_is_mod] at hdiv
  simp at hmod
  have h : (b &&& 128#u8) = 0#u8 ↔ b.val < 128 := by
    have hval : (b &&& 128#u8).val = 0#u8.val ↔ b.val < 128 := by
      simp only [UScalar.val_and]
      change (b.val &&& 128) = 0 ↔ b.val < 128
      omega
    exact ⟨fun h => hval.mp (congrArg UScalar.val h), fun h => scalar_eq_of_val (hval.mpr h)⟩
  simp [leb128fmt.is_last, lift, h]

private theorem byteAt_index {bytes : Slice U8} {idx : Nat} (h : idx < bytes.val.length) :
    byteAt bytes idx = bytes.val[idx].val := by simp [byteAt, h]

private theorem byte_lt_storage {b shift r storage : Nat} (hb : b < 2^r)
    (h : shift + r ≤ storage) : b * 2^shift < 2^storage := by
  calc
    b * 2^shift < 2^r * 2^shift := Nat.mul_lt_mul_of_pos_right hb (by positivity)
    _ = 2^(shift + r) := by rw [Nat.add_comm shift, Nat.pow_add]
    _ ≤ 2^storage := Nat.pow_le_pow_right (by decide) h

private theorem append_lt {value digit shift r : Nat}
    (hv : value < 2^shift) (hd : digit < 2^r) :
    value + digit * 2^shift < 2^(shift+r) := by
  have hm : (digit + 1) * 2^shift ≤ 2^r * 2^shift :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add, Nat.add_comm r] at hm
  omega


private def UIntReadInvariant {T : Type} (val : T → Nat) (width : U32)
    (bytes : Slice U8) (expected : Except Error (Nat × Nat))
    (state : T × U32 × Usize) : Prop :=
  ∃ group, 1 ≤ group ∧ group ≤ width.val / 7 ∧
    state.2.1.val = 7 * group ∧ val state.1 < 2^state.2.1.val ∧
    unsignedDigits bytes (width.val % 7) (width.val / 7 - group)
      state.2.2.val (2^state.2.1.val) (val state.1) = expected

private theorem unsigned_loop {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) (laws : UIntReaderLaws ops val storage) (width : U32)
    (hwidth : width.val ≤ storage) (hwidthLimit : storage ≤ 128)
    (hshiftLimit : 7 * (width.val / 7) < storage)
    (bytes : Slice U8) (start : Usize) (initial : T × U32 × Usize)
    (expected : Except Error (Nat × Nat))
    (hinv : UIntReadInvariant val width bytes expected initial) :
    WP.spec (leb128fmt.decode_uint_slice_loop width ops.shl ops.merge ops.byte bytes
      start initial.1 initial.2.1 initial.2.2)
      (fun out => UIntReaderPost val start expected (out.1, out.2.1)) := by
  unfold leb128fmt.decode_uint_slice_loop
  apply loop.spec_decr_nat (measure := fun state => bytes.val.length - state.2.2.val)
    (inv := UIntReadInvariant val width bytes expected)
  · rintro ⟨acc, shift, idx⟩ ⟨group, hgroupLow, hgroupHigh, hshift, hacc, hexpected⟩
    dsimp at *
    unfold leb128fmt.decode_uint_slice_loop.body
    have hshiftBound : shift.val < storage := by omega
    by_cases hend : bytes.val.length ≤ idx.val
    · have hend' : bytes.len ≤ idx := by scalar_tac
      rw [ite_eq_left hend']
      have he : expected = .error needMore := by
        rw [← hexpected]
        cases (width.val / 7 - group) <;> simp [unsignedDigits, hend]
      simp [he, UIntReaderPost]
    · have hend' : ¬bytes.len ≤ idx := by scalar_tac
      have hi : idx.val < bytes.val.length := by omega
      rw [ite_eq_right hend']
      step*
      · rename_i hlast hbad
        have he : shift.val = i2.val := congrArg UScalar.val hlast
        have hg : width.val / 7 - group = 0 := by omega
        have hpow : i3.val = 2 ^ (width.val % 7) := by
          have hr : width.val % 7 < 8 := by omega
          rw [i3_post, i1_post, Nat.shiftLeft_eq, Nat.one_mul]
          apply Nat.mod_eq_of_lt
          rw [U8.size, U8.numBits]
          exact Nat.pow_lt_pow_right (by decide) hr
        have hb : 2 ^ (width.val % 7) ≤ n.val := by scalar_tac
        rw [← hexpected, hg, unsignedDigits, ite_eq_right hend, byteAt_index hi, ← n_post, ite_eq_right (by omega)]
        exact ⟨rfl, rfl⟩
      · rename_i hlast hgood
        have he : shift.val = i2.val := congrArg UScalar.val hlast
        have hg : width.val / 7 - group = 0 := by omega
        have hpow : i3.val = 2 ^ (width.val % 7) := by
          have hr : width.val % 7 < 8 := by omega
          rw [i3_post, i1_post, Nat.shiftLeft_eq, Nat.one_mul]
          apply Nat.mod_eq_of_lt
          rw [U8.size, U8.numBits]
          exact Nat.pow_lt_pow_right (by decide) hr
        have hb : n.val < 2 ^ (width.val % 7) := by scalar_tac
        have hrem : width.val % 7 ≤ 7 := by omega
        have ht : n.val < 128 :=
          Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (n := 2) (by decide) hrem)
        obtain ⟨digit, shifted, out, hfrom, hshl, hor, hout⟩ :=
          laws.append acc n shift hshiftBound hacc
            (byte_lt_storage hb (by omega))
        simp [terminal_eq, ht, ← hlast, hfrom, hshl, hor]
        step*
        rw [← hexpected, hg, unsignedDigits, ite_eq_right hend, byteAt_index hi, ← n_post, ite_eq_left hb]
        exact ⟨hout, by omega⟩
      · rename_i hnotlast
        have he : shift.val ≠ i2.val := fun h => hnotlast (scalar_eq_of_val h)
        have hg : group < width.val / 7 := by omega
        have hf : width.val / 7 - group = (width.val / 7 - (group + 1)) + 1 := by omega
        by_cases ht : n.val < 128
        · obtain ⟨digit, shifted, out, hfrom, hshl, hor, hout⟩ :=
            laws.append acc n shift hshiftBound hacc
              (byte_lt_storage (r := 7) ht (by omega))
          simp [terminal_eq, ht, hfrom, hshl, hor]
          step*
          rw [← hexpected, hf, unsignedDigits, ite_eq_right hend, byteAt_index hi, ← n_post,
            ite_eq_left ht, Nat.mod_eq_of_lt ht]
          exact ⟨hout, by omega⟩
        · have hb : (n &&& 127#u8).val < 2^7 := by
            rw [low_payload]
            exact Nat.mod_lt _ (by decide)
          obtain ⟨digit, shifted, out, hfrom, hshl, hor, hout⟩ :=
            laws.append acc (n &&& 127#u8) shift hshiftBound hacc
              (byte_lt_storage hb (by omega))
          simp [terminal_eq, ht, lift, hfrom, hshl, hor]
          step*
          refine ⟨⟨group + 1, by omega, by omega, by dsimp; omega, ?_, ?_⟩, by omega⟩
          · rw [shift1_post, hout]
            exact append_lt hacc hb
          · rw [idx1_post, shift1_post, hout, low_payload, ← hexpected, hf, unsignedDigits,
              ite_eq_right hend, byteAt_index hi, ← n_post, ite_eq_right ht, Nat.pow_add]
            congr 1
            exact Nat.mul_comm _ _
  · exact hinv


/-- The release's effective group limit is one more than the quotient of the
    width by seven. A zero-bit final group accepts only a zero byte. -/
def unsignedReadExpected (width : Nat) (bytes : Slice U8) (start : Usize) :
    Except Error (Nat × Nat) :=
  unsignedDigits bytes (width % 7) (width / 7) start.val 1 0

theorem decode_uint_slice_spec {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) (laws : UIntReaderLaws ops val storage) (width : U32)
    (hwidth : width.val ≤ storage) (hwidthLimit : storage ≤ 128)
    (hwidthLow : 7 ≤ width.val) (hshiftLimit : 7 * (width.val / 7) < storage)
    (bytes : Slice U8) (start : Usize) :
    ∃ out, leb128fmt.decode_uint_slice width ops.shl ops.merge ops.byte ops.width bytes start = ok out ∧
      UIntReaderPost val start (unsignedReadExpected width.val bytes start) out := by
  apply total_result
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.size
  have hwidth' : width ≤ bits := UScalar.le_imp _ _ (by omega)
  have hfuel : width.val / 7 = (width.val / 7 - 1) + 1 := by omega
  unfold leb128fmt.decode_uint_slice unsignedReadExpected
  simp only [hbits]
  step*
  · rename_i hend'
    have hend : bytes.val.length ≤ start.val := by
      simpa only [UScalar.le_equiv, Slice.len_val] using hend'
    rw [hfuel, unsignedDigits, ite_eq_left hend]
    exact ⟨rfl, rfl⟩
  · rename_i hend'
    have hend : ¬bytes.val.length ≤ start.val := by
      simpa only [UScalar.le_equiv, Slice.len_val] using hend'
    have hi : start.val < bytes.val.length := by omega
    have he : byteAt bytes start.val = n.val := (byteAt_index hi).trans (congrArg UScalar.val n_post.symm)
    by_cases ht : n.val < 128
    · obtain ⟨out, hfrom, hout⟩ := laws.fromByte n
      simp [terminal_eq, ht, hfrom]
      step*
      rw [hfuel, unsignedDigits, ite_eq_right hend, he, ite_eq_left ht, Nat.mod_eq_of_lt ht]
      exact ⟨by simpa using hout, by omega⟩
    · obtain ⟨initial, hfrom, hout⟩ := laws.fromByte (n &&& 127#u8)
      have hacc : val initial < 128 := by
        rw [hout, low_payload]
        exact Nat.mod_lt _ (by decide)
      simp [terminal_eq, ht, lift, hfrom]
      step*
      let expected := unsignedDigits bytes (width.val % 7) (width.val / 7) start.val 1 0
      have hinv : UIntReadInvariant val width bytes expected (initial, 7#u32, idx) := by
        refine ⟨1, by omega, by omega, rfl, hacc, ?_⟩
        simp only [expected, idx_post, hout, low_payload]
        conv => rhs; rw [hfuel, unsignedDigits, ite_eq_right hend, he, ite_eq_right ht]
        simp
      obtain ⟨⟨out, p, flag⟩, hresult, hpost⟩ :=
        total_result (unsigned_loop ops val storage laws width hwidth hwidthLimit
          hshiftLimit bytes start (initial, 7#u32, idx) expected hinv)
      simpa [hresult] using hpost



/-- For a cursor at the end or a first byte that terminates, the release
    takes its fast path without consulting the number of field bits. -/
def unsignedFirstExpected (bytes : Slice U8) (start : Usize) :
    Except Error (Nat × Nat) :=
  if bytes.val.length ≤ start.val then .error needMore
  else .ok (byteAt bytes start.val, start.val+1)

private theorem decode_uint_slice_first {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) (laws : UIntReaderLaws ops val storage)
    (width : U32) (hwidth : width.val ≤ storage) (bytes : Slice U8) (start : Usize)
    (hcase : bytes.val.length ≤ start.val ∨ byteAt bytes start.val < 128) :
    ∃ out, leb128fmt.decode_uint_slice width ops.shl ops.merge ops.byte ops.width bytes start = ok out ∧
      UIntReaderPost val start (unsignedFirstExpected bytes start) out := by
  apply total_result
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.size
  have hwidth' : width ≤ bits := UScalar.le_imp _ _ (by omega)
  unfold leb128fmt.decode_uint_slice unsignedFirstExpected
  simp only [hbits]
  step*
  · rename_i hend'
    have hend : bytes.val.length ≤ start.val := by
      simpa only [UScalar.le_equiv, Slice.len_val] using hend'
    rw [ite_eq_left hend]
    exact ⟨rfl, rfl⟩
  · rename_i hend'
    have hend : ¬bytes.val.length ≤ start.val := by
      simpa only [UScalar.le_equiv, Slice.len_val] using hend'
    have hi : start.val < bytes.val.length := by omega
    have he : byteAt bytes start.val = n.val := (byteAt_index hi).trans (congrArg UScalar.val n_post.symm)
    have ht : n.val < 128 := he ▸ hcase.resolve_left hend
    obtain ⟨out, hfrom, hout⟩ := laws.fromByte n
    simp [terminal_eq, ht, hfrom, hend, he]
    step*
    exact ⟨hout, by omega⟩

private theorem decode_uint_slice_oversize {T : Type} (ops : UIntReaderOps T)
    (val : T → Nat) (storage : Nat) (laws : UIntReaderLaws ops val storage)
    (width : U32) (hwidth : storage < width.val) (bytes : Slice U8) (start : Usize) :
    leb128fmt.decode_uint_slice width ops.shl ops.merge ops.byte ops.width bytes start =
      fail .assertionFailure := by
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.size
  have hwidth' : ¬width ≤ bits := by
    rw [UScalar.le_equiv, hbitsVal]
    omega
  simp only [leb128fmt.decode_uint_slice, hbits, massert, Aeneas.Std.bind_ok,
    ite_eq_right hwidth', Aeneas.Std.bind_fail]

private theorem scalar_reader_laws {ty : UScalarTy}
    (ops : UIntReaderOps (UScalar ty))
    (hWidth : ∃ w, ops.width.BITS = ok w ∧ w.val = ty.numBits)
    (hFrom : ∀ b : U8, ∃ x, ops.byte.«from» b = ok x ∧ x.val = b.val)
    (hShift : ∀ (x : UScalar ty) (shift : U32), ops.shl.shl x shift = (x <<< shift))
    (hMerge : ∀ (x y : UScalar ty), ops.merge.bitor_assign x y = ok (x ||| y)) :
    UIntReaderLaws ops UScalar.val ty.numBits := by
  constructor
  · exact hWidth
  · intro acc b shift hshift hacc hb
    obtain ⟨digit, hdigit, hval⟩ := hFrom b
    have hspec : WP.spec (digit <<< shift) (fun shifted => shifted.val = b.val * 2^shift.val) := by
      obtain ⟨shifted, hr, hv, _⟩ :=
        total_result (UScalar.ShiftLeft_spec digit shift (UScalar.size ty) hshift rfl)
      rw [hr, WP.spec_ok, hv, hval, Nat.shiftLeft_eq, UScalar.size, Nat.mod_eq_of_lt hb]
    obtain ⟨shifted, hresult, hshifted⟩ := total_result hspec
    refine ⟨digit, shifted, acc ||| shifted, hdigit, (hShift _ _).trans hresult, hMerge _ _, ?_⟩
    rw [UScalar.val_or, hshifted, Nat.or_comm, Nat.mul_comm b.val, ← Nat.two_pow_add_eq_or_of_lt hacc,
      Nat.add_comm]
  · exact hFrom



private def u8_reader_ops : UIntReaderOps U8 where
  shl := U8.Insts.CoreOpsBitShlU32U8
  merge := U8.Insts.CoreOpsBitBitOrAssignU8
  byte := core.convert.FromSame U8
  width := U8.Insts.Leb128fmtUInt

private theorem u8_reader_laws : UIntReaderLaws u8_reader_ops (UScalar.val (ty := .U8)) 8 := by
  apply scalar_reader_laws
  · exact ⟨U8.Insts.Leb128fmtUInt.BITS, rfl, by
      rw [U8.Insts.Leb128fmtUInt.BITS]
      rfl⟩
  · intro b
    exact ⟨b, rfl, rfl⟩
  · intros
    rfl
  · intros
    rfl

theorem u8_reader_spec (width : U32) (bytes : Slice U8) (start : Usize)
    (hmin : 7 ≤ width.val) (hmax : width.val ≤ 8) :
    ∃ out, u8_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U8)) start (unsignedReadExpected width.val bytes start) out := by
  exact decode_uint_slice_spec u8_reader_ops UScalar.val 8 u8_reader_laws
    width hmax (by decide) hmin (by omega) bytes start

theorem u8_reader_first (width : U32) (bytes : Slice U8) (start : Usize)
    (hmax : width.val ≤ 8) (hcase : bytes.val.length ≤ start.val ∨ byteAt bytes start.val < 128) :
    ∃ out, u8_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U8)) start (unsignedFirstExpected bytes start) out := by
  exact decode_uint_slice_first u8_reader_ops UScalar.val 8 u8_reader_laws
    width hmax bytes start hcase

theorem u8_reader_oversize (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : 8 < width.val) :
    u8_reader width bytes start = fail .assertionFailure := by
  exact decode_uint_slice_oversize u8_reader_ops UScalar.val 8 u8_reader_laws
    width hwidth bytes start



private def u16_reader_ops : UIntReaderOps U16 where
  shl := U16.Insts.CoreOpsBitShlU32U16
  merge := U16.Insts.CoreOpsBitBitOrAssignU16
  byte := core.convert.FromU16U8
  width := U16.Insts.Leb128fmtUInt

private theorem u16_reader_laws : UIntReaderLaws u16_reader_ops (UScalar.val (ty := .U16)) 16 := by
  apply scalar_reader_laws
  · exact ⟨U16.Insts.Leb128fmtUInt.BITS, rfl, by
      rw [U16.Insts.Leb128fmtUInt.BITS]
      rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU16U8.from b, rfl, core.convert.num.FromU16U8.from_val_eq b⟩
  · intros
    rfl
  · intros
    rfl

theorem u16_reader_spec (width : U32) (bytes : Slice U8) (start : Usize)
    (hmin : 7 ≤ width.val) (hmax : width.val ≤ 16) :
    ∃ out, u16_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U16)) start (unsignedReadExpected width.val bytes start) out := by
  exact decode_uint_slice_spec u16_reader_ops UScalar.val 16 u16_reader_laws
    width hmax (by decide) hmin (by omega) bytes start

theorem u16_reader_first (width : U32) (bytes : Slice U8) (start : Usize)
    (hmax : width.val ≤ 16) (hcase : bytes.val.length ≤ start.val ∨ byteAt bytes start.val < 128) :
    ∃ out, u16_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U16)) start (unsignedFirstExpected bytes start) out := by
  exact decode_uint_slice_first u16_reader_ops UScalar.val 16 u16_reader_laws
    width hmax bytes start hcase

theorem u16_reader_oversize (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : 16 < width.val) :
    u16_reader width bytes start = fail .assertionFailure := by
  exact decode_uint_slice_oversize u16_reader_ops UScalar.val 16 u16_reader_laws
    width hwidth bytes start



private def u32_reader_ops : UIntReaderOps U32 where
  shl := U32.Insts.CoreOpsBitShlU32U32
  merge := U32.Insts.CoreOpsBitBitOrAssignU32
  byte := core.convert.FromU32U8
  width := U32.Insts.Leb128fmtUInt

private theorem u32_reader_laws : UIntReaderLaws u32_reader_ops (UScalar.val (ty := .U32)) 32 := by
  apply scalar_reader_laws
  · exact ⟨U32.Insts.Leb128fmtUInt.BITS, rfl, by
      rw [U32.Insts.Leb128fmtUInt.BITS]
      rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU32U8.from b, rfl, core.convert.num.FromU32U8.from_val_eq b⟩
  · intros
    rfl
  · intros
    rfl

theorem u32_reader_spec (width : U32) (bytes : Slice U8) (start : Usize)
    (hmin : 7 ≤ width.val) (hmax : width.val ≤ 32) :
    ∃ out, u32_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U32)) start (unsignedReadExpected width.val bytes start) out := by
  exact decode_uint_slice_spec u32_reader_ops UScalar.val 32 u32_reader_laws
    width hmax (by decide) hmin (by omega) bytes start

theorem u32_reader_first (width : U32) (bytes : Slice U8) (start : Usize)
    (hmax : width.val ≤ 32) (hcase : bytes.val.length ≤ start.val ∨ byteAt bytes start.val < 128) :
    ∃ out, u32_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U32)) start (unsignedFirstExpected bytes start) out := by
  exact decode_uint_slice_first u32_reader_ops UScalar.val 32 u32_reader_laws
    width hmax bytes start hcase

theorem u32_reader_oversize (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : 32 < width.val) :
    u32_reader width bytes start = fail .assertionFailure := by
  exact decode_uint_slice_oversize u32_reader_ops UScalar.val 32 u32_reader_laws
    width hwidth bytes start



private def u64_reader_ops : UIntReaderOps U64 where
  shl := U64.Insts.CoreOpsBitShlU32U64
  merge := U64.Insts.CoreOpsBitBitOrAssignU64
  byte := core.convert.FromU64U8
  width := U64.Insts.Leb128fmtUInt

private theorem u64_reader_laws : UIntReaderLaws u64_reader_ops (UScalar.val (ty := .U64)) 64 := by
  apply scalar_reader_laws
  · exact ⟨U64.Insts.Leb128fmtUInt.BITS, rfl, by
      rw [U64.Insts.Leb128fmtUInt.BITS]
      rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU64U8.from b, rfl, core.convert.num.FromU64U8.from_val_eq b⟩
  · intros
    rfl
  · intros
    rfl

theorem u64_reader_spec (width : U32) (bytes : Slice U8) (start : Usize)
    (hmin : 7 ≤ width.val) (hmax : width.val ≤ 64) :
    ∃ out, u64_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U64)) start (unsignedReadExpected width.val bytes start) out := by
  exact decode_uint_slice_spec u64_reader_ops UScalar.val 64 u64_reader_laws
    width hmax (by decide) hmin (by omega) bytes start

theorem u64_reader_first (width : U32) (bytes : Slice U8) (start : Usize)
    (hmax : width.val ≤ 64) (hcase : bytes.val.length ≤ start.val ∨ byteAt bytes start.val < 128) :
    ∃ out, u64_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U64)) start (unsignedFirstExpected bytes start) out := by
  exact decode_uint_slice_first u64_reader_ops UScalar.val 64 u64_reader_laws
    width hmax bytes start hcase

theorem u64_reader_oversize (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : 64 < width.val) :
    u64_reader width bytes start = fail .assertionFailure := by
  exact decode_uint_slice_oversize u64_reader_ops UScalar.val 64 u64_reader_laws
    width hwidth bytes start



private def u128_reader_ops : UIntReaderOps U128 where
  shl := U128.Insts.CoreOpsBitShlU32U128
  merge := U128.Insts.CoreOpsBitBitOrAssignU128
  byte := core.convert.FromU128U8
  width := U128.Insts.Leb128fmtUInt

private theorem u128_reader_laws : UIntReaderLaws u128_reader_ops (UScalar.val (ty := .U128)) 128 := by
  apply scalar_reader_laws
  · exact ⟨U128.Insts.Leb128fmtUInt.BITS, rfl, by
      rw [U128.Insts.Leb128fmtUInt.BITS]
      rfl⟩
  · intro b
    exact ⟨core.convert.num.FromU128U8.from b, rfl, core.convert.num.FromU128U8.from_val_eq b⟩
  · intros
    rfl
  · intros
    rfl

theorem u128_reader_spec (width : U32) (bytes : Slice U8) (start : Usize)
    (hmin : 7 ≤ width.val) (hmax : width.val ≤ 128) :
    ∃ out, u128_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U128)) start (unsignedReadExpected width.val bytes start) out := by
  exact decode_uint_slice_spec u128_reader_ops UScalar.val 128 u128_reader_laws
    width hmax (by decide) hmin (by omega) bytes start

theorem u128_reader_first (width : U32) (bytes : Slice U8) (start : Usize)
    (hmax : width.val ≤ 128) (hcase : bytes.val.length ≤ start.val ∨ byteAt bytes start.val < 128) :
    ∃ out, u128_reader width bytes start = ok out ∧
      UIntReaderPost (UScalar.val (ty := .U128)) start (unsignedFirstExpected bytes start) out := by
  exact decode_uint_slice_first u128_reader_ops UScalar.val 128 u128_reader_laws
    width hmax bytes start hcase

theorem u128_reader_oversize (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : 128 < width.val) :
    u128_reader width bytes start = fail .assertionFailure := by
  exact decode_uint_slice_oversize u128_reader_ops UScalar.val 128 u128_reader_laws
    width hwidth bytes start



abbrev UIntReadObservation := Except Error Nat × Nat

def observeUIntRead {T : Type} (val : T → Nat)
    (out : core.result.Result T Error × Usize) : UIntReadObservation :=
  ((match out.1 with
    | .Ok value => .ok (val value)
    | .Err error => .error error), out.2.val)

/-- Widths below seven never reach the field-width check after the first
    continuation. Each new radix digit is truncated to the storage width.
    An exhausted slice is checked before a shift by an invalid amount. -/
def smallUnsignedDigits (bytes : Slice U8) (storage start : Nat)
    (pos shift value : Nat) : Result UIntReadObservation :=
  if bytes.val.length ≤ pos then ok (.error needMore, start)
  else if shift < storage then
    let byte := byteAt bytes pos
    let next := value + (byte % 128 * 2^shift) % 2^storage
    if byte < 128 then ok (.ok next, pos + 1)
    else smallUnsignedDigits bytes storage start (pos + 1) (shift + 7) next
  else fail .integerOverflow
termination_by storage - shift
decreasing_by omega

structure SmallUIntReaderLaws {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) : Prop where
  append : ∀ (acc : T) (b : U8) (shift : U32),
    shift.val < storage → val acc < 2^shift.val →
    ∃ digit shifted out, ops.byte.«from» b = ok digit ∧
      ops.shl.shl digit shift = ok shifted ∧ ops.merge.bitor_assign acc shifted = ok out ∧
      val out = val acc + (b.val * 2^shift.val) % 2^storage
  invalidShift : ∀ (digit : T) (shift : U32), storage ≤ shift.val →
      ops.shl.shl digit shift = fail .integerOverflow

private theorem scalar_small_reader_laws {ty : UScalarTy} (ops : UIntReaderOps (UScalar ty))
    (hfrom : ∀ b : U8, ∃ x, ops.byte.«from» b = ok x ∧ x.val = b.val)
    (hshift : ∀ (x : UScalar ty) (shift : U32), ops.shl.shl x shift = (x <<< shift))
    (hmerge : ∀ (x y : UScalar ty), ops.merge.bitor_assign x y = ok (x ||| y)) :
    SmallUIntReaderLaws ops UScalar.val ty.numBits := by
  constructor
  · intro acc b shift hs hacc
    obtain ⟨digit, hdigit, hv⟩ := hfrom b
    obtain ⟨shifted, hresult, hval, _⟩ :=
      total_result (UScalar.ShiftLeft_spec digit shift (UScalar.size ty) hs rfl)
    rw [hv, Nat.shiftLeft_eq, UScalar.size] at hval
    refine ⟨digit, shifted, acc ||| shifted, hdigit, (hshift _ _).trans hresult, hmerge _ _, ?_⟩
    have hmultiple : (b.val * 2^shift.val) % 2^ty.numBits =
        b.val % 2^(ty.numBits - shift.val) * 2^shift.val := by
      conv => lhs; rw [show ty.numBits = (ty.numBits - shift.val) + shift.val by omega, Nat.pow_add]
      exact Nat.mul_mod_mul_right _ _ _
    rw [UScalar.val_or, hval, hmultiple, Nat.or_comm, Nat.mul_comm _ (2^shift.val),
      ← Nat.two_pow_add_eq_or_of_lt hacc, Nat.add_comm]
  · intro digit shift hs
    rw [hshift]
    simp [HShiftLeft.hShiftLeft, UScalar.shiftLeft_UScalar, UScalar.shiftLeft, show ¬shift.val < ty.numBits by omega]

private theorem small_loop_exact {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) (laws : UIntReaderLaws ops val storage)
    (small : SmallUIntReaderLaws ops val storage) (hstorage : storage ≤ 128)
    (width : U32) (hwidth : width.val < 7) (bytes : Slice U8) (start idx : Usize)
    (acc : T) (shift : U32) (hpositive : 0 < shift.val) (hacc : val acc < 2^shift.val) :
    (do
      let out ← leb128fmt.decode_uint_slice_loop width ops.shl ops.merge ops.byte bytes
        start acc shift idx
      ok (observeUIntRead val (out.1, out.2.1))) =
      smallUnsignedDigits bytes storage start.val idx.val shift.val (val acc) := by
  unfold leb128fmt.decode_uint_slice_loop
  rw [loop.eq_1, smallUnsignedDigits]
  dsimp only
  unfold leb128fmt.decode_uint_slice_loop.body
  dsimp only
  by_cases hend : bytes.val.length ≤ idx.val
  · have he : bytes.len ≤ idx := by scalar_tac
    simp [he, hend, observeUIntRead]
  · have he : ¬bytes.len ≤ idx := by scalar_tac
    have hi : idx.val < bytes.val.length := by omega
    obtain ⟨n, hn, hnv⟩ := total_result (Slice.index_usize_spec bytes idx hi)
    have hbyte : byteAt bytes idx.val = n.val := (byteAt_index hi).trans (congrArg UScalar.val hnv.symm)
    obtain ⟨r, hr, hv⟩ := total_result (U32.rem_spec width (y := 7#u32) (by decide))
    have hrEq : r = width := scalar_eq_of_val (hv.trans (Nat.mod_eq_of_lt hwidth))
    have hz : width - width = ok 0#u32 := by
      obtain ⟨v, hret, hval, _⟩ := total_result (U32.sub_spec (x := width) (y := width) (Nat.le_refl _))
      rw [hret, scalar_eq_of_val (by simpa using hval : v.val = (0#u32).val)]
    have hnz : shift ≠ 0#u32 := fun h => by simp [h] at hpositive
    rw [ite_eq_right hend, ite_eq_right he]
    simp only [hn, hr, Std.bind_ok, hrEq, hz, ite_eq_right hnz]
    by_cases hshift : shift.val < storage
    · rw [ite_eq_left hshift, hbyte]
      have hincrement : idx.val + 1 ≤ Usize.max := by
        have := bytes.length_ineq
        omega
      obtain ⟨nextIdx, hnextIdx, hnextIdxVal⟩ :=
        total_result (Usize.add_spec (x := idx) (y := 1#usize) hincrement)
      by_cases hterminal : n.val < 128
      · obtain ⟨digit, shifted, out, hfrom, hshl, hor, hout⟩ :=
          small.append acc n shift hshift hacc
        simp [terminal_eq, hterminal, hfrom, hshl, hor, hnextIdx, observeUIntRead,
          hnextIdxVal, hout, Nat.mod_eq_of_lt hterminal]
      · obtain ⟨digit, shifted, out, hfrom, hshl, hor, hout⟩ :=
          small.append acc (n &&& 127#u8) shift hshift hacc
        have hshiftAdd : shift.val + (7#u32).val ≤ U32.max := by
          rw [U32.max_eq]
          change shift.val + 7 ≤ 4294967295
          omega
        obtain ⟨nextShift, hnextShift, hnextShiftVal⟩ :=
          total_result (U32.add_spec (x := shift) (y := 7#u32) hshiftAdd)
        have hnewBound : val out < 2^nextShift.val := by
          have hp : (n &&& 127#u8).val < 2^7 := by
            rw [low_payload]
            exact Nat.mod_lt _ (by decide)
          rw [hnextShiftVal, hout]
          exact Nat.lt_of_le_of_lt
            (Nat.add_le_add_left (Nat.mod_le _ _) _)
            (append_lt hacc hp)
        have hnextPositive : 0 < nextShift.val := by
          change nextShift.val = shift.val + 7 at hnextShiftVal
          omega
        have ih := small_loop_exact ops val storage laws small hstorage width hwidth
          bytes start nextIdx out nextShift hnextPositive hnewBound
        rw [leb128fmt.decode_uint_slice_loop] at ih
        simp [terminal_eq, hterminal, lift, hfrom, hshl, hor, hnextIdx, hnextShift]
        have hmasked : n.val &&& 127 = n.val % 128 := Nat.and_two_pow_sub_one_eq_mod n.val 7
        simpa [leb128fmt.decode_uint_slice_loop.body, hr, hrEq, hz, terminal_eq, lift,
          hnextIdxVal, hnextShiftVal, hout, hmasked] using ih
    · rw [ite_eq_right hshift]
      by_cases hterminal : n.val < 128
      · obtain ⟨digit, hfrom, _⟩ := laws.fromByte n
        simp [terminal_eq, hterminal, hfrom, small.invalidShift digit shift (by omega)]
      · obtain ⟨digit, hfrom, _⟩ := laws.fromByte (n &&& 127#u8)
        simp [terminal_eq, hterminal, lift, hfrom, small.invalidShift digit shift (by omega)]
termination_by storage - shift.val
decreasing_by
  change nextShift.val = shift.val + 7 at hnextShiftVal
  omega



private theorem small_uint_slice_exact {T : Type} (ops : UIntReaderOps T) (val : T → Nat)
    (storage : Nat) (laws : UIntReaderLaws ops val storage)
    (small : SmallUIntReaderLaws ops val storage)
    (hstorage : 8 ≤ storage ∧ storage ≤ 128)
    (width : U32) (hwidth : width.val < 7) (bytes : Slice U8) (start : Usize) :
    (do
      let out ← leb128fmt.decode_uint_slice width ops.shl ops.merge ops.byte ops.width bytes start
      ok (observeUIntRead val out)) =
      smallUnsignedDigits bytes storage start.val start.val 0 0 := by
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.size
  have hwidth' : width.val ≤ bits.val := by omega
  unfold leb128fmt.decode_uint_slice
  rw [smallUnsignedDigits]
  by_cases hend : bytes.val.length ≤ start.val
  · have he : bytes.len ≤ start := by scalar_tac
    simp [hbits, hwidth', massert, he, hend, observeUIntRead]
  · have he : ¬bytes.len ≤ start := by scalar_tac
    have hi : start.val < bytes.val.length := by omega
    obtain ⟨n, hn, hnv⟩ := total_result (Slice.index_usize_spec bytes start hi)
    have hbyte : byteAt bytes start.val = n.val := (byteAt_index hi).trans (congrArg UScalar.val hnv.symm)
    have hincrement : start.val + 1 ≤ Usize.max := by
      have := bytes.length_ineq
      omega
    obtain ⟨idx, hidx, hidxVal⟩ :=
      total_result (Usize.add_spec (x := start) (y := 1#usize) hincrement)
    have hs : 0 < storage := by omega
    have hm : 128 ≤ 2^storage := Nat.pow_le_pow_right (n := 2) (by decide) (show 7 ≤ storage by omega)
    by_cases ht : n.val < 128
    · obtain ⟨read, hread, hval⟩ := laws.fromByte n
      simp [hbits, hwidth', massert, he, hn, hidx, hidxVal, hread, hval,
        terminal_eq, ht, observeUIntRead, hend, hs, hbyte, Nat.mod_eq_of_lt ht,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ht hm)]
    · obtain ⟨acc, hfrom, haccVal⟩ := laws.fromByte (n &&& 127#u8)
      have hmod : n.val % 128 < 128 := Nat.mod_lt _ (by decide)
      have hacc : val acc < 2^(7#u32).val := by rw [haccVal, low_payload]; exact hmod
      have ih := small_loop_exact ops val storage laws small hstorage.2 width hwidth bytes
        start idx acc 7#u32 (by decide) hacc
      simp [hbits, hwidth', massert, he, hn, hidx, terminal_eq, ht, hfrom, lift,
        hend, hs, hbyte, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hmod hm)]
      have hmasked : n.val &&& 127 = n.val % 128 := Nat.and_two_pow_sub_one_eq_mod n.val 7
      calc
        _ = (do
          let out ← leb128fmt.decode_uint_slice_loop width ops.shl ops.merge ops.byte bytes
            start acc 7#u32 idx
          ok (observeUIntRead val (out.1, out.2.1))) := by
            congr 1
            funext out
            rcases out with ⟨r, p, flag⟩
            simp
        _ = _ := by simpa [hidxVal, haccVal, hmasked] using ih



theorem u8_reader_small_width (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : width.val < 7) :
    (do
      let out ← u8_reader width bytes start
      ok (observeUIntRead (UScalar.val (ty := .U8)) out)) =
      smallUnsignedDigits bytes 8 start.val start.val 0 0 := by
  exact small_uint_slice_exact u8_reader_ops UScalar.val 8 u8_reader_laws
    (scalar_small_reader_laws u8_reader_ops u8_reader_laws.fromByte
      (by intros; rfl) (by intros; rfl))
    (by decide) width hwidth bytes start


theorem u16_reader_small_width (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : width.val < 7) :
    (do
      let out ← u16_reader width bytes start
      ok (observeUIntRead (UScalar.val (ty := .U16)) out)) =
      smallUnsignedDigits bytes 16 start.val start.val 0 0 := by
  exact small_uint_slice_exact u16_reader_ops UScalar.val 16 u16_reader_laws
    (scalar_small_reader_laws u16_reader_ops u16_reader_laws.fromByte
      (by intros; rfl) (by intros; rfl))
    (by decide) width hwidth bytes start


theorem u32_reader_small_width (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : width.val < 7) :
    (do
      let out ← u32_reader width bytes start
      ok (observeUIntRead (UScalar.val (ty := .U32)) out)) =
      smallUnsignedDigits bytes 32 start.val start.val 0 0 := by
  exact small_uint_slice_exact u32_reader_ops UScalar.val 32 u32_reader_laws
    (scalar_small_reader_laws u32_reader_ops u32_reader_laws.fromByte
      (by intros; rfl) (by intros; rfl))
    (by decide) width hwidth bytes start


theorem u64_reader_small_width (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : width.val < 7) :
    (do
      let out ← u64_reader width bytes start
      ok (observeUIntRead (UScalar.val (ty := .U64)) out)) =
      smallUnsignedDigits bytes 64 start.val start.val 0 0 := by
  exact small_uint_slice_exact u64_reader_ops UScalar.val 64 u64_reader_laws
    (scalar_small_reader_laws u64_reader_ops u64_reader_laws.fromByte
      (by intros; rfl) (by intros; rfl))
    (by decide) width hwidth bytes start


theorem u128_reader_small_width (width : U32) (bytes : Slice U8) (start : Usize)
    (hwidth : width.val < 7) :
    (do
      let out ← u128_reader width bytes start
      ok (observeUIntRead (UScalar.val (ty := .U128)) out)) =
      smallUnsignedDigits bytes 128 start.val start.val 0 0 := by
  exact small_uint_slice_exact u128_reader_ops UScalar.val 128 u128_reader_laws
    (scalar_small_reader_laws u128_reader_ops u128_reader_laws.fromByte
      (by intros; rfl) (by intros; rfl))
    (by decide) width hwidth bytes start

end leb128fmt.sliceProof
