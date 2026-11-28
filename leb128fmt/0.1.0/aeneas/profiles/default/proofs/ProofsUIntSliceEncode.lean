import SliceConcrete

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow
open leb128fmt_slice_probe

namespace leb128fmt.sliceProof

theorem total_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

theorem scalar_eq_of_val {ty : UScalarTy} {x y : UScalar ty} (h : x.val = y.val) : x = y := by
  cases x with
  | mk xv =>
    cases y with
    | mk yv => congr 1; exact BitVec.eq_of_toNat_eq h

def byteAt (bytes : Slice U8) (i : Nat) : Nat := (bytes.val[i]?.getD 0#u8).val

theorem byteAt_set (bytes : Slice U8) (idx : Usize) (value : U8) (i : Nat)
    (hi : i < bytes.val.length) :
    byteAt (bytes.set idx value) i = if i = idx.val then value.val else byteAt bytes i := by
  simp only [byteAt, Slice.set_val_eq, List.getElem?_set]
  split <;> simp_all [eq_comm]

def unsignedByte (value index : Nat) : Nat :=
  value / 128 ^ index % 128 + if 128 ^ (index + 1) ≤ value then 128 else 0

def SliceWritten (byte : Nat → Nat) (before : Slice U8) (start count : Nat) (after : Slice U8) : Prop :=
  after.val.length = before.val.length ∧
  ∀ i, i < before.val.length →
    byteAt after i = if start ≤ i ∧ i < start + count then byte (i - start) else byteAt before i

theorem written_zero (byte : Nat → Nat) (before : Slice U8) (start : Nat) :
    SliceWritten byte before start 0 before := by
  refine ⟨rfl, ?_⟩
  intro i hi
  simp only [Nat.add_zero]
  rw [ite_eq_right (by omega)]

theorem written_append {byte : Nat → Nat} {before after : Slice U8} {start : Nat} {idx : Usize}
    {b : U8} (hpos : start ≤ idx.val) (_hidx : idx.val < before.val.length)
    (hwrite : SliceWritten byte before start (idx.val - start) after)
    (hb : b.val = byte (idx.val - start)) :
    SliceWritten byte before start (idx.val + 1 - start) (after.set idx b) := by
  obtain ⟨hlen, hbytes⟩ := hwrite
  refine ⟨by simpa [Slice.set_val_eq] using hlen, ?_⟩
  intro i hi
  rw [byteAt_set _ _ _ _ (by omega), hbytes i hi]
  by_cases he : i = idx.val
  · rw [he, ite_eq_left rfl, ite_eq_left (by omega)]
    exact hb
  · rw [ite_eq_right he]
    have hp : (start ≤ i ∧ i < start + (idx.val - start)) ↔
        start ≤ i ∧ i < start + (idx.val + 1 - start) := by omega
    simp only [hp]

def UIntWritten (value : Nat) (before : Slice U8) (start : Usize)
    (out : Option Usize × Slice U8 × Usize) : Prop :=
  match out.1 with
  | none =>
    out.2.2 = start ∧
    (before.val.length = start.val ∨ 128 ^ (before.val.length - start.val) ≤ value) ∧
    SliceWritten (unsignedByte value) before start.val (before.val.length - start.val) out.2.1
  | some count =>
    0 < count.val ∧ count.val + start.val = out.2.2.val ∧ out.2.2.val ≤ before.val.length ∧
    value < 128 ^ count.val ∧ (1 < count.val → 128 ^ (count.val - 1) ≤ value) ∧
    SliceWritten (unsignedByte value) before start.val count.val out.2.1

structure UIntWriterOps (T E : Type) where
  eq : core.cmp.PartialEq T T
  and : core.ops.bit.BitAnd T T T
  shr : leb128fmt_slice_probe.core.ops.bit.Shr T U32 T
  shrAssign : leb128fmt_slice_probe.core.ops.bit.ShrAssign T U32
  fromByteTrait : core.convert.From T U8
  type : leb128fmt_slice_probe.leb128fmt.UInt T
  convert : core.convert.TryFrom U8 T E

structure UIntWriterLaws {T E : Type} (op : UIntWriterOps T E) (val : T → Nat)
    (storage : Nat) : Prop where
  size : ∃ bits, op.type.BITS = ok bits ∧ bits.val = storage
  bounds : ∀ x, val x < 2 ^ storage
  fromByte : ∀ b : U8, ∃ x, op.fromByteTrait.«from» b = ok x ∧ val x = b.val
  lowMask : ∀ x mask, val mask = 127 → ∃ out, op.and.bitand x mask = ok out ∧ val out = val x % 128
  shift : ∀ x (n : U32), n.val < storage →
    ∃ out, op.shr.shr x n = ok out ∧ val out = val x / 2 ^ n.val
  lowShift : ∀ x, ∃ out, op.shrAssign.shr_assign x 7#u32 = ok out ∧ val out = val x / 128
  equal : ∀ x y, op.eq.eq x y = ok (decide (val x = val y))
  unequal : ∀ x y, op.eq.ne x y = ok (decide (val x ≠ val y))
  narrow : ∀ x, val x < 256 →
    ∃ b, op.convert.try_from x = ok (.Ok b) ∧ b.val = val x

private def UIntLoopInvariant {T : Type} (val : T → Nat) (value : Nat)
    (before : Slice U8) (start : Usize) (state : T × Slice U8 × Usize) : Prop :=
  start.val ≤ state.2.2.val ∧ state.2.2.val ≤ before.val.length ∧
  val state.1 = value / 128 ^ (state.2.2.val - start.val) ∧
  (start.val < state.2.2.val → 128 ^ (state.2.2.val - start.val) ≤ value) ∧
  SliceWritten (unsignedByte value) before start.val (state.2.2.val - start.val) state.2.1

private theorem unsigned_body_eq {T E : Type} (op : UIntWriterOps T E) (zero value : T)
    (output : Slice U8) (start idx : Usize) (hzero : op.fromByteTrait.«from» 0#u8 = ok zero) :
    leb128fmt.encode_uint_slice_loop1.body op.eq op.and op.shrAssign op.fromByteTrait op.convert
        start value output idx =
      leb128fmt.encode_uint_slice_loop0.body op.eq op.and op.shrAssign op.fromByteTrait op.convert
        zero start value output idx := by
  unfold leb128fmt.encode_uint_slice_loop1.body leb128fmt.encode_uint_slice_loop0.body
  simp [hzero]

private theorem unsigned_loop_spec {T E : Type} (op : UIntWriterOps T E) (val : T → Nat)
    (storage : Nat) (laws : UIntWriterLaws op val storage) (value zero : T)
    (before : Slice U8) (start : Usize) (hstart : start.val ≤ before.val.length)
    (hzero : val zero = 0) :
    WP.spec (leb128fmt.encode_uint_slice_loop0 op.eq op.and op.shrAssign op.fromByteTrait op.convert
      zero value before start start) (UIntWritten (val value) before start) := by
  unfold leb128fmt.encode_uint_slice_loop0
  apply loop.spec_decr_nat (measure := fun state => before.val.length - state.2.2.val)
    (inv := UIntLoopInvariant val (val value) before start)
  · rintro ⟨rest, out, idx⟩ ⟨hlow, hhigh, hrest, hcontinue, hbytes⟩
    dsimp at *
    unfold leb128fmt.encode_uint_slice_loop0.body
    by_cases hfull : out.len ≤ idx
    · rw [ite_eq_left hfull]
      simp only [WP.spec_ok, UIntWritten]
      have he : idx.val = before.val.length := by
        obtain ⟨hlen, _⟩ := hbytes
        scalar_tac
      refine ⟨trivial, ?_, ?_⟩
      · by_cases hp : start.val < idx.val
        · exact Or.inr (by simpa [he] using hcontinue hp)
        · exact Or.inl (by omega)
      · simpa [he] using hbytes
    · rw [ite_eq_right hfull]
      obtain ⟨mask, hmask, hm⟩ := laws.fromByte 127#u8
      obtain ⟨digit, hmasking, hd⟩ := laws.lowMask rest mask hm
      have hdigit : val digit < 128 := by rw [hd]; exact Nat.mod_lt _ (by decide)
      obtain ⟨byte, hconvert, hb⟩ := laws.narrow digit (by omega)
      obtain ⟨next, hshift, hnext⟩ := laws.lowShift rest
      have hn : val next = val value / 128 ^ (idx.val - start.val + 1) := by
        rw [hnext, hrest, Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hcompare := laws.equal next zero
      rw [hzero] at hcompare
      have hlen := hbytes.1
      have hidx : idx.val < before.val.length := by scalar_tac
      by_cases hdone : val next = 0 <;>
        simp [hmask, hmasking, hconvert, hshift, hcompare, hdone] <;> step*
      · have hsmall : val value < 128 ^ (idx.val - start.val + 1) := by
          have hq : val value / 128 ^ (idx.val - start.val + 1) = 0 := hn.symm.trans hdone
          exact (Nat.div_eq_zero_iff.mp hq).resolve_left (by positivity)
        have hbyte : byte.val = unsignedByte (val value) (idx.val - start.val) := by
          unfold unsignedByte
          rw [ite_eq_right (by omega), Nat.add_zero, hb, hd, hrest]
        have hlen' : len.val = idx.val - start.val + 1 := by omega
        simp only [UIntWritten, index_mut_back_post]
        refine ⟨by omega, by omega, by omega, by simpa [hlen'] using hsmall, ?_, ?_⟩
        · intro hk
          rw [hlen', Nat.add_sub_cancel]
          exact hcontinue (by omega)
        · rw [len_post, index1_post]
          exact written_append hlow hidx hbytes hbyte
      · have hlarge : 128 ^ (idx.val - start.val + 1) ≤ val value := by
          apply Nat.le_of_not_gt
          intro h
          exact hdone (hn.trans (Nat.div_eq_of_lt h))
        have hbyte : (byte ||| 128#u8).val =
            unsignedByte (val value) (idx.val - start.val) := by
          simp only [UScalar.val_or, unsignedByte, hlarge, ite_true, ← hrest]
          have ht : byte.val < 128 := hb.symm ▸ hdigit
          change byte.val ||| 128 = val rest % 128 + 128
          rw [Nat.or_two_pow_eq_add_of_lt (n := 7) ht, hb, hd]
        simp only [UIntLoopInvariant, index_mut_back_post, index1_post]
        have hp : idx.val + 1 - start.val = idx.val - start.val + 1 := by omega
        refine ⟨⟨by omega, by omega, by simpa [hp] using hn, ?_, ?_⟩, by omega⟩
        · intro _
          simpa [hp] using hlarge
        · exact written_append hlow hidx hbytes hbyte
  · refine ⟨Nat.le_refl _, hstart, ?_, by simp, ?_⟩
    · simp
    · simpa using written_zero (unsignedByte (val value)) before start.val

def UIntWriterPost (width value : Nat) (before : Slice U8) (start : Usize)
    (out : Option Usize × Slice U8 × Usize) : Prop :=
  if value < 2^width then UIntWritten value before start out
  else out = (none, before, start)

theorem encode_uint_slice_spec {T E : Type} (op : UIntWriterOps T E) (val : T → Nat)
    (storage : Nat) (laws : UIntWriterLaws op val storage) (width : U32) (value : T)
    (before : Slice U8) (start : Usize) (hstart : start.val ≤ before.val.length)
    (hwidth : width.val ≤ storage) :
    ∃ out, leb128fmt.encode_uint_slice width op.eq op.and op.shr op.shrAssign
        op.fromByteTrait op.type op.eq op.convert value before start = ok out ∧
      UIntWriterPost width.val (val value) before start out := by
  apply total_result
  obtain ⟨storageWidth, hstorage, hstorageVal⟩ := laws.size
  obtain ⟨zero, hzero, hzeroVal⟩ := laws.fromByte 0#u8
  have hzeroVal' : val zero = 0 := hzeroVal
  have hloop := unsigned_loop_spec op val storage laws value zero before start hstart hzeroVal'
  unfold leb128fmt.encode_uint_slice
  simp [hstorage]
  by_cases hlt : width.val < storageWidth.val
  · have hsmall : width.val < storage := by scalar_tac
    obtain ⟨shifted, hshift, hshiftValue⟩ := laws.shift value width hsmall
    have hcmp := laws.unequal shifted zero
    rw [hzeroVal', hshiftValue] at hcmp
    by_cases hfit : val value < 2^width.val
    · have hq : val value / 2^width.val = 0 := Nat.div_eq_of_lt hfit
      have hp : UIntWriterPost width.val (val value) before start =
          UIntWritten (val value) before start := by funext out; simp [UIntWriterPost, hfit]
      rw [hp]
      simpa [hlt, hshift, hzero, hcmp, hq] using hloop
    · have hq : val value / 2^width.val ≠ 0 := by
        intro h
        exact hfit ((Nat.div_eq_zero_iff.mp h).resolve_left (by positivity))
      simp [hlt, hshift, hzero, hcmp, hq, UIntWriterPost, hfit]
  · have he : width.val = storage := by scalar_tac
    have hfit : val value < 2^width.val := by rw [he]; exact laws.bounds value
    have hbody : (fun (state : T × Slice U8 × Usize) =>
        leb128fmt.encode_uint_slice_loop1.body op.eq op.and op.shrAssign op.fromByteTrait
          op.convert start state.1 state.2.1 state.2.2) =
        (fun (state : T × Slice U8 × Usize) =>
        leb128fmt.encode_uint_slice_loop0.body op.eq op.and op.shrAssign op.fromByteTrait
          op.convert zero start state.1 state.2.1 state.2.2) := by
      funext state
      exact unsigned_body_eq op zero state.1 state.2.1 start state.2.2 hzero
    have hp : UIntWriterPost width.val (val value) before start =
        UIntWritten (val value) before start := by funext out; simp [UIntWriterPost, hfit]
    simp only [ite_eq_right hlt, hp]
    unfold leb128fmt.encode_uint_slice_loop1
    rw [hbody]
    exact hloop

def u8_writer_ops : UIntWriterOps U8 Never where
  eq := core.cmp.PartialEqU8
  and := U8.Insts.CoreOpsBitBitAndU8U8
  shr := U8.Insts.CoreOpsBitShrU32U8
  shrAssign := U8.Insts.CoreOpsBitShrAssignU32
  fromByteTrait := core.convert.FromSame U8
  type := U8.Insts.Leb128fmtUInt
  convert := core.convert.TryFromTUNever.Blanket (core.convert.IntoFrom (core.convert.FromSame U8))

theorem u8_writer_laws : UIntWriterLaws u8_writer_ops (UScalar.val (ty := .U8)) 8 := by
  constructor
  · exact ⟨U8.Insts.Leb128fmtUInt.BITS, rfl, by rw [U8.Insts.Leb128fmtUInt.BITS]; rfl⟩
  · intro x
    scalar_tac
  · intro b
    exact ⟨b, rfl, rfl⟩
  · intro x mask hm
    refine ⟨x &&& mask, rfl, ?_⟩
    rw [UScalar.val_and, hm]
    exact Nat.and_two_pow_sub_one_eq_mod x.val 7
  · intro x n hn
    apply total_result
    change WP.spec (x >>> n) _
    step*
  · intro x
    apply total_result
    change WP.spec (x >>> 7#u32) _
    step*
  · intro x y
    change ok (decide (x = y)) = _
    by_cases he : x.val = y.val
    · simp [scalar_eq_of_val he]
    · have hne : x ≠ y := fun h => he (congrArg UScalar.val h)
      simp [he, hne]
  · intro x y
    change ok (decide (x ≠ y)) = _
    by_cases he : x.val = y.val
    · simp [scalar_eq_of_val he]
    · have hne : x ≠ y := fun h => he (congrArg UScalar.val h)
      simp [he, hne]
  · intro x _
    exact ⟨x, by simp [u8_writer_ops, core.convert.TryFromTUNever.Blanket,
      core.convert.TryFromTUNever.Blanket.try_from, core.convert.IntoFrom,
      core.convert.FromSame], rfl⟩

theorem u8_writer_spec (width : U32) (value : U8) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hwidth : width.val ≤ 8) :
    ∃ out, u8_writer width value before start = ok out ∧
      UIntWriterPost width.val value.val before start out := by
  exact encode_uint_slice_spec u8_writer_ops (UScalar.val (ty := .U8)) 8 u8_writer_laws
    width value before start hstart hwidth

end leb128fmt.sliceProof
