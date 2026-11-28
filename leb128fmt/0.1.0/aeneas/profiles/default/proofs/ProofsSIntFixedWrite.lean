import SignedWriteCommon

open Aeneas Aeneas.Std Aeneas.Std.WP Result ControlFlow

namespace leb128fmt.sliceProof

private def flaggedDigit (x : Int) (j : Nat) : Nat := signedDigit x j + 128

private def FixedPayloadInv {T : Type} (val : T → Int) (x : Int) (count : Nat)
    (before : Slice U8) (start : Usize) (s : T × Slice U8 × Usize) : Prop :=
  start.val ≤ s.2.2.val ∧ s.2.2.val - start.val < count ∧
  val s.1 = x / (128 : Int)^(s.2.2.val - start.val) ∧
  SignedWritten (flaggedDigit x) before start.val (s.2.2.val-start.val) s.2.1

private def FixedPayloadPost (x : Int) (count : Nat) (before : Slice U8) (start : Usize)
    (s : Usize × Bool × Slice U8) : Prop :=
  ∃ k, 0 < k ∧ k ≤ count ∧ s.1.val = start.val+k ∧
    x / (128 : Int)^k = (if s.2.1 then -1 else 0) ∧
    SignedWritten (flaggedDigit x) before start.val k s.2.2

private theorem signed_fixed_payload {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (v zero minusOne : T) (hz : val zero = 0) (hm : val minusOne = -1)
    (before : Slice U8) (start : Usize) (count : Nat) (hcount : 0 < count)
    (hfit : SignedFits (val v) (count-1)) (hspace : start.val+count ≤ before.val.length) :
    WP.spec (encode_fixed_sint_slice_loop0 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero minusOne v before start) (FixedPayloadPost (val v) count before start) := by
  unfold encode_fixed_sint_slice_loop0
  apply loop.spec_decr_nat (measure := fun s => count - (s.2.2.val-start.val))
    (inv := FixedPayloadInv val (val v) count before start)
  · rintro ⟨rest, output, index⟩ ⟨hstart, hindex, hrest, hwrite⟩
    dsimp at *
    have hbound : index.val < before.val.length := by omega
    have hlen := hwrite.1
    have hout : index.val < output.val.length := by omega
    obtain ⟨mask, digit, b, next, hmask, hdigit, hb, hnext, hbVal, hnextVal⟩ :=
      digit_step ops val storage laws rest
    have hd : b.val = (val rest % 128).toNat := by omega
    have hsmall : b.val < 128 := by omega
    have hq : val next = val v / (128 : Int)^(index.val-start.val+1) := by
      rw [hnextVal, hrest, next_rest]
    have hfinish : SignedFits (val v) (index.val-start.val) ↔
        (val next = 0 ∧ b.val < 64) ∨ (val next = -1 ∧ 64 ≤ b.val) := by
      rw [fits_rest, ← hrest, end_condition, ← hnextVal, ← hbVal]
      omega
    have hbyte : (b ||| 128#u8).val = flaggedDigit (val v) (index.val-start.val) := by
      rw [continuation_digit _ hsmall, hd, hrest]
      rfl
    have hsz := laws.equal next zero
    have hsm := laws.equal next minusOne
    rw [hz] at hsz
    rw [hm] at hsm
    unfold encode_fixed_sint_slice_loop0.body
    have hsign := sign_mask b hsmall
    by_cases he0 : val next = 0 <;> by_cases hem : val next = -1 <;>
      by_cases hs : b &&& 64#u8 = 0#u8 <;>
      simp [hmask, hdigit, hb, hnext, hsz, hsm, he0, hem, hs, lift] <;> step*
    all_goals
      have hw := written_next hstart hwrite hbyte
      have hj : index1.val-start.val = index.val-start.val+1 := by omega
      have hj' : index.val+1-start.val = index.val-start.val+1 := by omega
      simp only [FixedPayloadInv, FixedPayloadPost, index_mut_back_post]
      first
      | refine ⟨index.val-start.val+1, by omega, by omega, by omega, ?_, ?_⟩
        · rw [← hq]
          first
          | exact he0
          | exact hem
        · simpa only [hj'] using hw
      | have hnot : ¬SignedFits (val v) (index.val-start.val) := fun h => by
          have hterm := hfinish.mp h
          first
          | have hb' := hsign.mp hs
            omega
          | have hb' := mt hsign.mpr hs
            omega
        have hn : index.val-start.val+1 < count := by
          by_contra! h
          have he : index.val-start.val = count-1 := by omega
          exact hnot (he ▸ hfit)
        refine ⟨⟨by omega, by omega, by rw [hj, ← hq], ?_⟩, by omega⟩
        simpa only [hj, hj'] using hw
  · exact ⟨le_rfl, by simpa, by simp, by simpa using written_empty (flaggedDigit (val v)) before start.val⟩

private def SignedPadInv (x : Int) (count : Nat) (negative : Bool)
    (before : Slice U8) (start : Usize) (s : Slice U8 × Usize) : Prop :=
  start.val ≤ s.2.val ∧ s.2.val ≤ start.val+count ∧
    x / (128 : Int)^(s.2.val-start.val) = (if negative then -1 else 0) ∧
    SignedWritten (flaggedDigit x) before start.val (s.2.val-start.val) s.1

private def SignedPadPost (x : Int) (count : Nat)
    (before : Slice U8) (start : Usize) (s : Slice U8 × Usize) : Prop :=
  s.2.val = start.val+count ∧ SignedWritten (flaggedDigit x) before start.val count s.1

private theorem padByteVal (x : Int) (j : Nat) (negative : Bool)
    (hquot : x / (128 : Int)^j = (if negative then -1 else 0)) :
    (if negative then 255#u8 else 128#u8).val = flaggedDigit x j := by
  unfold flaggedDigit signedDigit
  rw [hquot]
  cases negative <;> rfl

private theorem fixed_pad_loop (x : Int) (count : Usize) (negative : Bool)
    (before output : Slice U8) (start index : Usize)
    (hspace : start.val+count.val ≤ before.val.length)
    (hinv : SignedPadInv x count.val negative before start (output,index)) :
    WP.spec (encode_fixed_sint_slice_loop1 count output start index negative)
      (SignedPadPost x count.val before start) := by
  unfold encode_fixed_sint_slice_loop1
  apply loop.spec_decr_nat (measure := fun s => start.val + count.val - s.2.val)
    (inv := SignedPadInv x count.val negative before start)
  · rintro ⟨buf, idx⟩ ⟨hlow, hhigh, hq, hwrite⟩
    dsimp at *
    have hlen := hwrite.1
    unfold encode_fixed_sint_slice_loop1.body
    step as ⟨endpoint, hendpoint⟩
    by_cases heq : idx = endpoint
    · have hv := congrArg UScalar.val heq
      simp [heq, SignedPadPost]
      refine ⟨by omega, ?_⟩
      have hh : idx.val-start.val = count.val := by omega
      rwa [hh] at hwrite
    · have hlt : idx.val < buf.val.length := by
        have hn : idx.val ≠ endpoint.val := mt (scalar_eq_of_val) heq
        omega
      let byte := if negative then 255#u8 else 128#u8
      have hupdate :
          (if negative then Slice.update buf idx 255#u8 else Slice.update buf idx 128#u8) =
            Slice.update buf idx byte := by cases negative <;> rfl
      rw [ite_eq_right heq, hupdate]
      step*
      have hwritten := written_next hlow hwrite (padByteVal x _ negative hq)
      have hn : index1.val-start.val = idx.val-start.val+1 := by omega
      have hne : idx.val ≠ endpoint.val := mt scalar_eq_of_val heq
      have hltEnd : idx.val < start.val + count.val := by
        rw [hendpoint] at hne
        omega
      have hlo' : start.val ≤ index1.val := by
        rw [index1_post]
        exact Nat.le_trans hlow (Nat.le_succ _)
      have hhi' : index1.val ≤ start.val + count.val := by
        rw [index1_post]
        exact Nat.succ_le_of_lt hltEnd
      simp only [SignedPadInv, output1_post]
      refine ⟨⟨hlo', hhi', ?_, ?_⟩, ?_⟩
      · rw [hn, ← next_rest, hq]
        cases negative <;> rfl
      · rw [index1_post]
        exact hwritten
      · rw [index1_post]
        omega
  · exact hinv

private theorem clearFinalFrame (x : Int) (count : Nat)
    (before output : Slice U8) (start idx : Usize) (b : U8)
    (hcount : 0 < count) (hspace : start.val+count ≤ before.val.length)
    (hidx : idx.val = start.val+count-1)
    (hb : b.val = sliceByte output idx.val)
    (hwrite : SignedWritten (flaggedDigit x) before start.val count output) :
    SignedWritten (signedFixedByte x count) before start.val count
      (output.set idx (b &&& 127#u8)) := by
  obtain ⟨hlen, hbytes⟩ := hwrite
  have hidx' : idx.val < before.val.length := by omega
  have hflagged : b.val = flaggedDigit x (count-1) := by
    rw [hb, hbytes _ hidx', ite_eq_left (by omega), show idx.val-start.val = count-1 by omega]
  have hsmall : signedDigit x (count-1) < 128 := by
    unfold signedDigit
    omega
  have hm : (b &&& 127#u8).val = signedDigit x (count-1) := by
    rw [UScalar.val_and]
    change b.val &&& 127 = _
    rw [show b.val &&& 127 = b.val % 128 from Nat.and_two_pow_sub_one_eq_mod b.val 7,
      hflagged, flaggedDigit]
    omega
  refine ⟨by simpa [Slice.set_val_eq] using hlen, ?_⟩
  intro j hj
  rw [sliceByte_set _ _ _ _ (by omega)]
  by_cases hji : j = idx.val
  · rw [hji, ite_eq_left rfl, ite_eq_left (by omega), hm, signedFixedByte,
      show idx.val-start.val = count-1 by omega, ite_eq_right (by omega), Nat.add_zero]
  · rw [ite_eq_right hji, hbytes j hj]
    split
    · simp [flaggedDigit, signedFixedByte, show j-start.val+1 < count by omega]
    · rfl

def SignedFixedWriterPost (width : Nat) (x : Int) (before : Slice U8) (start : Usize)
    (out : Option Usize × Slice U8 × Usize) : Prop :=
  let count := (width+6)/7
  if start.val+count ≤ before.val.length then
    ∃ written, out.1 = some written ∧ written.val = count ∧
      out.2.2.val = start.val+count ∧
      SignedWritten (signedFixedByte x count) before start.val count out.2.1
  else out = (none, before, start)

private theorem fixed_after_guard {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (width : U32) (v zero minusOne : T) (hz : val zero = 0) (hm : val minusOne = -1)
    (before : Slice U8) (start : Usize) (hstart : start.val ≤ before.val.length)
    (hw : 0 < width.val) (hfit : SignedFits (val v) ((width.val+6)/7-1)) :
    WP.spec (do
      let suffix ← core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) before { start := start }
      let count ← max_len width
      if Slice.len suffix < count then ok (none, before, start)
      else
        let (idx, negative, buf) ← encode_fixed_sint_slice_loop0 ops.eq ops.mask
          ops.shiftAssign ops.fromSignedByte ops.narrow zero minusOne v before start
        let (padded, finish) ← encode_fixed_sint_slice_loop1 count buf start idx negative
        let finalIndex ← finish - 1#usize
        let finalByte ← Slice.index_usize padded finalIndex
        let masked ← lift (finalByte &&& 127#u8)
        let output ← Slice.update padded finalIndex masked
        let len ← finish - start
        ok (some len, output, finish))
      (SignedFixedWriterPost width.val (val v) before start) := by
  have hr : ({ start := start } : core.ops.range.RangeFrom Usize).start ≤ before.length := hstart
  rw [Slice.index_SliceIndexRangeFromUsizeSliceInst]
  apply WP.spec_bind (core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec _ before hr)
  intro suffix ⟨_, hsuffix⟩
  obtain ⟨count, hcount, hcountVal⟩ := signed_slice_max_len width
  simp only [hcount, Aeneas.Std.bind_ok]
  change suffix.val.length = before.val.length-start.val at hsuffix
  by_cases hshort : suffix.len < count
  · have hh : suffix.val.length < count.val := hshort
    have hcap : ¬start.val + (width.val+6)/7 ≤ before.val.length := by omega
    simp [hshort, SignedFixedWriterPost, hcap]
  · have hh : ¬suffix.val.length < count.val := hshort
    have hcap : start.val + (width.val+6)/7 ≤ before.val.length := by omega
    have hspace : start.val+count.val ≤ before.val.length := by omega
    have hpos : 0 < count.val := by omega
    rw [ite_eq_right hshort]
    apply WP.spec_bind (signed_fixed_payload ops val storage laws v zero minusOne hz hm before start
      count.val hpos (by rwa [hcountVal]) hspace)
    rintro ⟨idx, negative, buf⟩ h
    obtain ⟨k, hk, hkle, hidx, hq, hwritten⟩ := h
    dsimp at hidx hq hwritten
    have hk' : idx.val-start.val = k := by omega
    have hpad : SignedPadInv (val v) count.val negative before start (buf,idx) := by
      unfold SignedPadInv
      dsimp only [Prod.fst, Prod.snd]
      exact ⟨by omega, by omega, by rwa [hk'], by rwa [hk']⟩
    apply WP.spec_bind (fixed_pad_loop (val v) count negative before buf start idx hspace hpad)
    rintro ⟨padded, finish⟩ ⟨hfinish, hframe⟩
    dsimp at hfinish hframe
    have hlen := hframe.1
    step*
    have hbyte : finalByte.val = sliceByte padded finalIndex.val := by
      rw [finalByte_post]
      unfold sliceByte
      rw [List.getElem?_eq_getElem (by omega)]
      rfl
    have hclear := clearFinalFrame (val v) count.val before padded start finalIndex finalByte
        hpos hspace (by omega) hbyte hframe
    have heq : masked = finalByte &&& 127#u8 := scalar_eq_of_val masked_post
    simp only [SignedFixedWriterPost, hcap, ↓reduceIte, output_post, heq]
    refine ⟨len, rfl, by omega, by omega, ?_⟩
    simpa only [hcountVal] using hclear

private theorem payload2_eq {T E : Type} (ops : SignedGuardOps T E)
    (zero minusOne v : T) (before : Slice U8) (start : Usize)
    (hm : ops.fromSignedByte.«from» (-1)#i8 = ok minusOne) :
    encode_fixed_sint_slice_loop2 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero v before start =
    encode_fixed_sint_slice_loop0 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero minusOne v before start := by
  unfold encode_fixed_sint_slice_loop2 encode_fixed_sint_slice_loop0
  congr 1
  funext state
  rcases state with ⟨rest, out, idx⟩
  simp [encode_fixed_sint_slice_loop2.body, encode_fixed_sint_slice_loop0.body, hm]

private theorem payload4_eq {T E : Type} (ops : SignedGuardOps T E)
    (zero minusOne v : T) (before : Slice U8) (start : Usize)
    (hz : ops.fromSignedByte.«from» 0#i8 = ok zero)
    (hm : ops.fromSignedByte.«from» (-1)#i8 = ok minusOne) :
    encode_fixed_sint_slice_loop4 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow v before start =
    encode_fixed_sint_slice_loop0 ops.eq ops.mask ops.shiftAssign ops.fromSignedByte
      ops.narrow zero minusOne v before start := by
  unfold encode_fixed_sint_slice_loop4 encode_fixed_sint_slice_loop0
  congr 1
  funext state
  rcases state with ⟨rest, out, idx⟩
  simp [encode_fixed_sint_slice_loop4.body, encode_fixed_sint_slice_loop0.body, hz, hm]

/-- The checked fixed writer for values admitted by the release guard.
    When the buffer can hold the fixed representation, the value must fit
    in its groups. The capacity failure never needs that premise. -/
theorem signed_fixed_slice_of_guard {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (width : U32) (v : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val)
    (hguard : SignedGuardAccepts storage width.val (val v))
    (hfit : start.val+(width.val+6)/7 ≤ before.val.length →
      SignedFits (val v) ((width.val+6)/7-1)) :
    ∃ out, encode_fixed_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v before start = ok out ∧
      SignedFixedWriterPost width.val (val v) before start out := by
  by_cases hroom : start.val+(width.val+6)/7 ≤ before.val.length
  · apply successful_result
    obtain ⟨bits, hbits, hbitsVal⟩ := laws.bits
    obtain ⟨zero, hzero, hz⟩ := laws.signedByte 0#i8
    obtain ⟨minusOne, hminusOne, hm⟩ := laws.signedByte (-1)#i8
    have hafter := fixed_after_guard ops val storage laws width v zero minusOne hz hm
      before start hstart hw (hfit hroom)
    unfold encode_fixed_sint_slice
    simp only [hbits, Aeneas.Std.bind_ok]
    by_cases hsmall : width < bits
    · have hlt : width.val < bits.val := hsmall
      have hrange : -(2^width.val : Int) ≤ val v ∧ val v < (2^width.val : Int) := by
        rcases hguard with h | h
        · omega
        · exact h
      obtain ⟨shifted, hshift, hshiftVal⟩ := laws.arithmeticRight v width (by omega)
      have he0 := laws.unequal shifted zero
      have hem := laws.unequal shifted minusOne
      rw [hz] at he0
      rw [hm] at hem
      rcases signed_guard_quotient (by positivity) hrange with hq | hq
      · have hev : val shifted = 0 := hshiftVal.trans hq
        rw [ite_eq_left hsmall]
        simp [hshift, hzero, he0, hev, payload2_eq _ _ _ _ _ _ hminusOne]
        exact hafter
      · have hev : val shifted = -1 := hshiftVal.trans hq
        rw [ite_eq_left hsmall]
        simp [hshift, hzero, hminusOne, he0, hem, hev]
        exact hafter
    · rw [ite_eq_right hsmall]
      rw [payload4_eq _ _ _ _ _ _ hzero hminusOne]
      exact hafter
  · have hshort : before.val.length - start.val < (width.val+6)/7 := by omega
    exact ⟨(none,before,start),
      signed_fixed_writer_short ops val storage laws.toSignedGuardLaws width v before start hstart hshort,
      by simp [SignedFixedWriterPost, hroom]⟩

/-- For all widths in the intended domain, characterize the release guard
    rejection as well as the fixed encoding and short-capacity outcomes. -/
theorem encode_fixed_sint_slice_spec {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (width : U32) (v : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (_hwidth : width.val ≤ storage)
    (hfit : SignedGuardAccepts storage width.val (val v) →
      start.val + (width.val+6)/7 ≤ before.val.length →
      SignedFits (val v) ((width.val+6)/7-1)) :
    ∃ out, encode_fixed_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v before start = ok out ∧
      (if SignedGuardAccepts storage width.val (val v)
        then SignedFixedWriterPost width.val (val v) before start out
        else out = (none, before, start)) := by
  by_cases ha : SignedGuardAccepts storage width.val (val v)
  · obtain ⟨out, hresult, hpost⟩ :=
      signed_fixed_slice_of_guard ops val storage laws width v before start hstart hw ha (hfit ha)
    exact ⟨out, hresult, by simpa [ha] using hpost⟩
  · have hh : width.val < storage := by
      apply Nat.lt_of_not_ge
      exact fun h => ha (Or.inl h)
    have houtside : val v < -(2^width.val : Int) ∨ (2^width.val : Int) ≤ val v := by
      have hnot := fun h => ha (Or.inr h)
      omega
    obtain ⟨_, hresult⟩ := signed_writers_reject ops val storage laws.toSignedGuardLaws
      width v before start hh houtside
    exact ⟨(none, before, start), hresult, by simp [ha]⟩

/-- For the intended signed field, representability establishes the bound on
    the payload loop's length. Both success and capacity failure are total. -/
theorem signed_fixed_slice_spec {T E : Type} (ops : SignedGuardOps T E)
    (val : T → Int) (storage : Nat) (laws : SignedWriterLaws ops val storage)
    (width : U32) (v : T) (before : Slice U8) (start : Usize)
    (hstart : start.val ≤ before.val.length) (hw : 0 < width.val) (_hwidth : width.val ≤ storage)
    (hvalue : -(2^(width.val-1) : Int) ≤ val v ∧ val v < (2^(width.val-1) : Int)) :
    ∃ out, encode_fixed_sint_slice width ops.eq ops.mask ops.shift ops.shiftAssign
      ops.fromSignedByte ops.integer ops.eq ops.narrow v before start = ok out ∧
      SignedFixedWriterPost width.val (val v) before start out := by
  apply signed_fixed_slice_of_guard ops val storage laws width v before start hstart hw
  · exact guard_accepts_of_representable storage width.val (val v) hvalue
  · intro _
    exact fixed_fits_of_representable width.val (val v) hw hvalue

end leb128fmt.sliceProof
