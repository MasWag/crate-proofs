import SintSlices

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow

namespace leb128fmt.sliceProof

theorem successful_result {α : Type _} {m : Result α} {p : α → Prop}
    (h : WP.spec m p) : ∃ value, m = Result.ok value ∧ p value := by
  cases m using Result.cases with
  | ret value => exact ⟨value, rfl, WP.spec_ok value |>.mp h⟩
  | vis effect k => exact False.elim ((WP.spec_vis effect k).mp h)
  | div => exact False.elim (WP.spec_div.mp h)

structure SignedGuardOps (T E : Type) where
  eq : core.cmp.PartialEq T T
  mask : core.ops.bit.BitAnd T T T
  shift : leb128fmt.core.ops.bit.Shr T U32 T
  shiftAssign : leb128fmt.core.ops.bit.ShrAssign T U32
  fromSignedByte : core.convert.From T I8
  integer : leb128fmt.SInt T
  narrow : core.convert.TryFrom U8 T E

structure SignedGuardLaws {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) : Prop where
  bits : ∃ w, ops.integer.BITS = ok w ∧ w.val = storage
  signedByte : ∀ b : I8, ∃ x, ops.fromSignedByte.«from» b = ok x ∧ val x = b.val
  arithmeticRight : ∀ (x : T) (w : U32), w.val < storage →
    ∃ shifted, ops.shift.shr x w = ok shifted ∧ val shifted = val x / (2^w.val : Int)
  unequal : ∀ x y, ops.eq.ne x y = ok (decide (val x ≠ val y))

private theorem shifted_outside {x bound : Int} (hpos : 0 < bound)
    (h : x < -bound ∨ bound ≤ x) : x / bound ≠ 0 ∧ x / bound ≠ -1 := by
  have he := Int.mul_ediv_add_emod x bound
  have hlo := Int.emod_nonneg x (by omega : bound ≠ 0)
  have hhi := Int.emod_lt_of_pos x hpos
  constructor <;> intro heq <;> simp [heq] at he <;> omega

/-- The out-of-range guard precedes the shortest and fixed writer's first
    narrowing conversion. Its range is the release's wider signed interval. -/
theorem signed_writers_reject {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedGuardLaws ops val storage)
    (width : U32) (v : T) (bytes : Slice U8) (start : Usize)
    (hwidth : width.val < storage)
    (houtside : val v < -(2^width.val : Int) ∨ (2^width.val : Int) ≤ val v) :
    leb128fmt.encode_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v bytes start = ok (none, bytes, start) ∧
    leb128fmt.encode_fixed_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v bytes start = ok (none, bytes, start) := by
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.bits
  obtain ⟨x, hx, hxVal⟩ := laws.arithmeticRight v width hwidth
  obtain ⟨zero, hzero, hzeroVal⟩ := laws.signedByte 0#i8
  obtain ⟨negOne, hnegOne, hnegOneVal⟩ := laws.signedByte (-1)#i8
  have hguard : width.val < bits.val := by omega
  obtain ⟨hneZero, hneNegOne⟩ := shifted_outside (by positivity) houtside
  have hne0 : ops.eq.ne x zero = ok true := by
    rw [laws.unequal, hxVal, hzeroVal]
    simp [hneZero]
  have hne1 : ops.eq.ne x negOne = ok true := by
    rw [laws.unequal, hxVal, hnegOneVal]
    simp [hneNegOne]
  constructor <;> simp [leb128fmt.encode_sint_slice, leb128fmt.encode_fixed_sint_slice,
    hbits, hguard, hx, hzero, hnegOne, hne0, hne1]

theorem signed_slice_max_len (width : U32) :
    ∃ count, leb128fmt.max_len width = ok count ∧ count.val = (width.val + 6) / 7 := by
  apply successful_result
  unfold leb128fmt.max_len
  step as ⟨remainder, hrem⟩
  by_cases hz : remainder = 0#u32
  · have hzero : width.val % 7 = 0 := by rw [← hrem, hz]; rfl
    simp only [hz, ite_true]
    step*
  · have hnz : width.val % 7 ≠ 0 := by
      intro he
      apply hz
      apply UScalar.eq_imp
      rw [hrem]
      exact he
    simp only [ite_eq_right hz]
    step*

/-- Under the scalar guard laws, the fixed writer returns through the
    capacity check independently of the masking and narrowing operations. -/
theorem signed_fixed_writer_short {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedGuardLaws ops val storage)
    (width : U32) (v : T) (bytes : Slice U8) (start : Usize)
    (hstart : start.val ≤ bytes.val.length)
    (hshort : bytes.val.length - start.val < (width.val + 6) / 7) :
    leb128fmt.encode_fixed_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v bytes start = ok (none, bytes, start) := by
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.bits
  obtain ⟨count, hcount, hcountVal⟩ := signed_slice_max_len width
  have hs : ({ start := start } : core.ops.range.RangeFrom Usize).start ≤ bytes.length := hstart
  obtain ⟨suffix, hsuffix, _, hsuffixLen⟩ :=
    successful_result (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec _ bytes hs)
  have hlt : suffix.val.length < count.val := by
    change suffix.val.length = bytes.val.length - start.val at hsuffixLen
    omega
  by_cases hwidth : width.val < bits.val
  · obtain ⟨x, hx, _⟩ := laws.arithmeticRight v width (by omega)
    obtain ⟨zero, hzero, _⟩ := laws.signedByte 0#i8
    obtain ⟨negOne, hnegOne, _⟩ := laws.signedByte (-1)#i8
    rw [leb128fmt.encode_fixed_sint_slice]
    simp [hbits, hx, hzero, hnegOne, laws.unequal,
      Slice.index_SliceIndexRangeFromUsizeSliceInst, hsuffix, hcount, hlt]
  · simp [leb128fmt.encode_fixed_sint_slice, hbits, hwidth,
      Slice.index_SliceIndexRangeFromUsizeSliceInst, hsuffix, hcount, hlt]


/-- A full destination stops the shortest writer before any narrowing call. -/
theorem signed_shortest_writer_full {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedGuardLaws ops val storage)
    (width : U32) (v : T) (bytes : Slice U8) (start : Usize)
    (hfull : bytes.val.length ≤ start.val) :
    leb128fmt.encode_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v bytes start = ok (none, bytes, start) := by
  have hfull' : bytes.len ≤ start := by scalar_tac
  have h0 (zero negOne : T) :
      leb128fmt.encode_sint_slice_loop0 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
        ops.narrow zero negOne v bytes start start = ok (none, bytes, start) := by
    unfold leb128fmt.encode_sint_slice_loop0
    rw [loop.eq_1]
    unfold leb128fmt.encode_sint_slice_loop0.body
    simp [hfull']
  have h1 (zero : T) :
      leb128fmt.encode_sint_slice_loop1 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
        ops.narrow zero v bytes start start = ok (none, bytes, start) := by
    unfold leb128fmt.encode_sint_slice_loop1
    rw [loop.eq_1]
    unfold leb128fmt.encode_sint_slice_loop1.body
    simp [hfull']
  have h2 :
      leb128fmt.encode_sint_slice_loop2 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
        ops.narrow v bytes start start = ok (none, bytes, start) := by
    unfold leb128fmt.encode_sint_slice_loop2
    rw [loop.eq_1]
    unfold leb128fmt.encode_sint_slice_loop2.body
    simp [hfull']
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.bits
  by_cases hwidth : width.val < bits.val
  · obtain ⟨x, hx, _⟩ := laws.arithmeticRight v width (by omega)
    obtain ⟨zero, hzero, _⟩ := laws.signedByte 0#i8
    obtain ⟨negOne, hnegOne, _⟩ := laws.signedByte (-1)#i8
    simp [leb128fmt.encode_sint_slice, hbits, hwidth, hx, hzero, hnegOne, laws.unequal, h0, h1]
  · simp [leb128fmt.encode_sint_slice, hbits, hwidth, h2]

end leb128fmt.sliceProof
