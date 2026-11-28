import SignedWriteCommon

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow

namespace leb128fmt.sliceProof

private theorem shortest_body1_eq {T E : Type} (ops : SignedGuardOps T E)
    (zero negOne : T) (hneg : ops.fromSignedByte.«from» (-1)#i8 = ok negOne)
    (start idx : Usize) (rest : T) (out : Slice U8) :
    leb128fmt.encode_sint_slice_loop1.body ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero start rest out idx =
    leb128fmt.encode_sint_slice_loop0.body ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero negOne start rest out idx := by
  simp [leb128fmt.encode_sint_slice_loop1.body, leb128fmt.encode_sint_slice_loop0.body, hneg]

private theorem shortest_body2_eq {T E : Type} (ops : SignedGuardOps T E)
    (zero negOne : T) (hzero : ops.fromSignedByte.«from» 0#i8 = ok zero)
    (hneg : ops.fromSignedByte.«from» (-1)#i8 = ok negOne)
    (start idx : Usize) (rest : T) (out : Slice U8) :
    leb128fmt.encode_sint_slice_loop2.body ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow start rest out idx =
    leb128fmt.encode_sint_slice_loop0.body ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero negOne start rest out idx := by
  simp [leb128fmt.encode_sint_slice_loop2.body, leb128fmt.encode_sint_slice_loop0.body, hzero, hneg]

def SignedShortestWritten (value : Int) (before : Slice U8) (start : Usize)
    (out : Option Usize × Slice U8 × Usize) : Prop :=
  match out.1 with
  | none =>
    out.2.2 = start ∧
    (∀ j, j < before.val.length - start.val → ¬SignedFits value j) ∧
    SignedWritten (signedShortestByte value) before start.val (before.val.length - start.val) out.2.1
  | some count =>
    0 < count.val ∧ count.val + start.val = out.2.2.val ∧ out.2.2.val ≤ before.val.length ∧
    SignedFits value (count.val - 1) ∧
    (∀ j, j < count.val - 1 → ¬SignedFits value j) ∧
    SignedWritten (signedShortestByte value) before start.val count.val out.2.1

private def ShortestInv {T : Type} (val : T → Int) (value : Int) (before : Slice U8)
    (start : Usize) (state : T × Slice U8 × Usize) : Prop :=
  start.val ≤ state.2.2.val ∧ state.2.2.val ≤ before.val.length ∧
  val state.1 = value / 128^(state.2.2.val - start.val) ∧
  (∀ j, j < state.2.2.val - start.val → ¬SignedFits value j) ∧
  SignedWritten (signedShortestByte value) before start.val (state.2.2.val - start.val) state.2.1

private theorem shortest_loop {T E : Type} (ops : SignedGuardOps T E) (val : T → Int)
    (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (value zero negOne : T) (hzeroVal : val zero = 0) (hnegVal : val negOne = -1)
    (before : Slice U8) (start : Usize) (hstart : start.val ≤ before.val.length) :
    WP.spec (leb128fmt.encode_sint_slice_loop0 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero negOne value before start start) (SignedShortestWritten (val value) before start) := by
  unfold leb128fmt.encode_sint_slice_loop0
  apply loop.spec_decr_nat (measure := fun state => before.val.length - state.2.2.val)
    (inv := ShortestInv val (val value) before start)
  · rintro ⟨rest, out, idx⟩ ⟨hlo, hhi, hrest, hprev, hwrite⟩
    dsimp at *
    unfold leb128fmt.encode_sint_slice_loop0.body
    have hlen := hwrite.1
    by_cases hfull : out.len ≤ idx
    · rw [ite_eq_left hfull]
      simp only [WP.spec_ok, SignedShortestWritten]
      have he : idx.val = before.val.length := by scalar_tac
      exact ⟨trivial, by simpa [he] using hprev, by simpa [he] using hwrite⟩
    · rw [ite_eq_right hfull]
      have hidx : idx.val < before.val.length := by scalar_tac
      obtain ⟨mask, digit, byte, next, hmask, hdigit, hbyte, hshift, hb, hn⟩ :=
        digit_step ops val storage laws rest
      have hbyteLt : byte.val < 128 := by omega
      have heq0 := laws.equal next zero
      have heqn := laws.equal next negOne
      rw [hzeroVal] at heq0
      rw [hnegVal] at heqn
      have hmaskTest := sign_mask_val byte hbyteLt
      have hfitIff : SignedFits (val value) (idx.val - start.val) ↔
          (val next = 0 ∧ byte.val < 64) ∨ (val next = -1 ∧ 64 ≤ byte.val) := by
        rw [fits_rest, ← hrest, end_condition, ← hn, ← hb]
        omega
      have hb' : byte.val = signedDigit (val value) (idx.val - start.val) := by
        unfold signedDigit
        rw [← hrest, ← hb]
        rfl
      have hn' : val next = val value / 128^(idx.val - start.val + 1) := by
        rw [hn, hrest, next_rest]
      by_cases hz : val next = 0 <;> by_cases hm : val next = -1 <;>
        by_cases hs : byte.val < 64 <;>
        simp [hmask, hdigit, hbyte, hshift, heq0, heqn, hz, hm, hmaskTest, hs, lift] <;> step*
      all_goals
        first
        | have hf : SignedFits (val value) (idx.val - start.val) := hfitIff.mpr (by omega)
          have hbyteValue : byte.val = signedShortestByte (val value) (idx.val - start.val) := by
            simp [signedShortestByte, hf, hb']
          have hlen' : len.val - 1 = idx.val - start.val := by omega
          simp only [SignedShortestWritten, s_post]
          refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
          · simpa only [hlen'] using hf
          · simpa only [hlen'] using hprev
          · rw [len_post, index1_post]
            exact written_next hlo hwrite hbyteValue
        | have hf : ¬SignedFits (val value) (idx.val - start.val) := by
            intro h
            have := hfitIff.mp h
            omega
          have hbyteValue : (byte ||| 128#u8).val =
              signedShortestByte (val value) (idx.val - start.val) := by
            rw [continuation_digit byte hbyteLt, signedShortestByte, ite_eq_right hf, hb']
          have hi' : idx.val + 1 - start.val = idx.val - start.val + 1 := by omega
          simp only [ShortestInv, s_post, index1_post]
          refine ⟨⟨by omega, by omega, ?_, ?_, written_next hlo hwrite hbyteValue⟩, by omega⟩
          · simpa only [hi'] using hn'
          · intro j hj
            by_cases h : j < idx.val - start.val
            · exact hprev j h
            · have he : j = idx.val - start.val := by omega
              simpa only [he] using hf
  · refine ⟨Nat.le_refl _, hstart, by simp, by simp, ?_⟩
    simpa using written_empty (signedShortestByte (val value)) before start.val


def SignedShortestPost (storage width : Nat) (value : Int) (before : Slice U8) (start : Usize)
    (out : Option Usize × Slice U8 × Usize) : Prop :=
  if SignedGuardAccepts storage width value then SignedShortestWritten value before start out
  else out = (none, before, start)

theorem encode_sint_slice_spec {T E : Type} (ops : SignedGuardOps T E) (val : T → Int)
    (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (width : U32) (value : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) :
    ∃ out, leb128fmt.encode_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow value before start = ok out ∧
      SignedShortestPost storage width.val (val value) before start out := by
  apply successful_result
  obtain ⟨bits, hbits, hbitsVal⟩ := laws.bits
  obtain ⟨zero, hzero, hzeroVal⟩ := laws.signedByte 0#i8
  obtain ⟨negOne, hneg, hnegVal⟩ := laws.signedByte (-1)#i8
  have hzeroVal' : val zero = 0 := hzeroVal
  have hnegVal' : val negOne = -1 := hnegVal
  have h0 := shortest_loop ops val storage laws value zero negOne hzeroVal' hnegVal'
    before start hstart
  have h1 : WP.spec (leb128fmt.encode_sint_slice_loop1 ops.eq ops.mask ops.shiftAssign
      ops.fromSignedByte ops.narrow zero value before start start)
      (SignedShortestWritten (val value) before start) := by
    unfold leb128fmt.encode_sint_slice_loop1
    have he : (fun (state : T × Slice U8 × Usize) =>
        leb128fmt.encode_sint_slice_loop1.body ops.eq ops.mask ops.shiftAssign
          ops.fromSignedByte ops.narrow zero start state.1 state.2.1 state.2.2) =
        (fun (state : T × Slice U8 × Usize) =>
          leb128fmt.encode_sint_slice_loop0.body ops.eq ops.mask ops.shiftAssign
            ops.fromSignedByte ops.narrow zero negOne start state.1 state.2.1 state.2.2) := by
      funext state
      exact shortest_body1_eq ops zero negOne hneg start state.2.2 state.1 state.2.1
    rw [he]
    exact h0
  have h2 : WP.spec (leb128fmt.encode_sint_slice_loop2 ops.eq ops.mask ops.shiftAssign
      ops.fromSignedByte ops.narrow value before start start)
      (SignedShortestWritten (val value) before start) := by
    unfold leb128fmt.encode_sint_slice_loop2
    have he : (fun (state : T × Slice U8 × Usize) =>
        leb128fmt.encode_sint_slice_loop2.body ops.eq ops.mask ops.shiftAssign
          ops.fromSignedByte ops.narrow start state.1 state.2.1 state.2.2) =
        (fun (state : T × Slice U8 × Usize) =>
          leb128fmt.encode_sint_slice_loop0.body ops.eq ops.mask ops.shiftAssign
            ops.fromSignedByte ops.narrow zero negOne start state.1 state.2.1 state.2.2) := by
      funext state
      exact shortest_body2_eq ops zero negOne hzero hneg start state.2.2 state.1 state.2.1
    rw [he]
    exact h0
  by_cases hguard : SignedGuardAccepts storage width.val (val value)
  · have hpost : SignedShortestPost storage width.val (val value) before start =
        SignedShortestWritten (val value) before start := by
      funext out
      simp [SignedShortestPost, hguard]
    rw [hpost]
    by_cases hw : width.val < storage
    · obtain ⟨v, hv, hvVal⟩ := laws.arithmeticRight value width hw
      have hrange := hguard.resolve_left (by omega)
      have hq := signed_guard_quotient (by positivity) hrange
      have hw' : width.val < bits.val := by omega
      rcases hq with hq | hq
      · have heq : ops.eq.ne v zero = ok false := by
          simp [laws.unequal, hvVal, hq, hzeroVal']
        simpa [leb128fmt.encode_sint_slice, hbits, hw', hv, hzero, heq] using h1
      · have hne : ops.eq.ne v zero = ok true := by
          simp [laws.unequal, hvVal, hq, hzeroVal']
        have heq : ops.eq.ne v negOne = ok false := by
          simp [laws.unequal, hvVal, hq, hnegVal']
        simpa [leb128fmt.encode_sint_slice, hbits, hw', hv, hzero, hneg, hne, heq] using h0
    · have hw' : ¬width.val < bits.val := by omega
      simpa [leb128fmt.encode_sint_slice, hbits, hw'] using h2
  · have hfailure := signed_writers_reject ops val storage laws.toSignedGuardLaws width value
        before start (by by_contra h; exact hguard (Or.inl (by omega)))
        (by by_contra h; apply hguard; exact Or.inr (by omega))
    simp [hfailure.1, SignedShortestPost, hguard]

end leb128fmt.sliceProof
