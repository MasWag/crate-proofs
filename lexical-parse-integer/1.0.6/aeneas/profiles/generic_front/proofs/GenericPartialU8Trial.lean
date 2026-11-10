import GenericDigit
import GenericScalarSpecs
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness
open lexical_parse_integer_generic_harness
namespace GenericPartialU8Trial
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
open LexicalParseIntegerGenericSpec

private theorem u8_max_255 : U8.max = 255 := U8.max_eq

def agreesU8 (r : core.result.Result (U8 × Usize) lexical_util.error.Error) : ScanResult → Prop
  | .value n consumed => match r with | .Ok x => x.1.val = n ∧ x.2.val = consumed | _ => False
  | .invalidDigit _ => False
  | .overflow i => match r with | .Err (.Overflow j) => j.val = i | _ => False
  | .underflow _ => False

def scanU8 (radix : U32) (it : core.slice.iter.Iter U8) (value : U8) (cursor : Usize) : ScanResult :=
  scan radix.val U8.max false true ((it.slice.val.drop it.i).map UScalar.val) value.val cursor.val

def invU8 (radix : U32) (target : ScanResult)
    (x : core.slice.iter.Iter U8 × U8 × Usize) : Prop :=
  x.1.i ≤ x.1.slice.val.length ∧
  x.2.2.val + (x.1.slice.val.length - x.1.i) ≤ Usize.max ∧
  scanU8 radix x.1 x.2.1 x.2.2 = target

theorem partial.checked_u8_partial_loop_spec (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (it : core.slice.iter.Iter U8) (value : U8) (cursor : Usize)
    (hi : it.i ≤ it.slice.val.length)
    (hsafe : cursor.val + (it.slice.val.length - it.i) ≤ Usize.max) :
    partial.checked_u8_partial_loop it value cursor radix
      ⦃ out => agreesU8 out (scanU8 radix it value cursor) ⦄ := by
  unfold partial.checked_u8_partial_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.Iter U8 × U8 × Usize) => x.1.slice.val.length - x.1.i)
    (inv := invU8 radix (scanU8 radix it value cursor))
  · intro x hx
    rcases x with ⟨it', value', cursor'⟩
    dsimp [invU8] at hx
    obtain ⟨hi', hsafe', htarget⟩ := hx
    dsimp only
    unfold partial.checked_u8_partial_loop.body
    by_cases hn : it'.i < it'.slice.val.length
    · have heq : core.slice.iter.IteratorSliceIter.next it' =
        .ok (some it'.slice.val[it'.i], {it' with i := it'.i+1}) := by
        simp [core.slice.iter.IteratorSliceIter.next, hn]; rfl
      rw [heq]
      simp only [bind_ok]
      step as ⟨cursor1, hcursor⟩
      obtain ⟨d, hdcall, hd⟩ := LexicalDigitProofs.char_to_digit_const_spec
        it'.slice.val[it'.i] radix hr
      rw [hdcall]
      simp only [bind_ok]
      cases d with
      | none =>
        step as ⟨idx, hidx⟩
        rw [←htarget]
        simp only [scanU8, List.drop_eq_getElem_cons hn, List.map_cons, scan]
        simp only [Option.map_none] at hd
        rw [←hd]
        simp [agreesU8]
        omega
      | some digit =>
        simp only [Option.map_some] at hd
        have hbound : digit.val < radix.val := by
          have h := hd
          unfold LexicalParseIntegerDigitSpec.digit at h
          cases ha : LexicalParseIntegerDigitSpec.asciiValue it'.slice.val[it'.i].val with
          | none => simp [ha] at h
          | some v =>
            simp [ha] at h
            exact h.2 ▸ h.1
        have hscan : scanU8 radix it' value' cursor' =
          if radix.val * value'.val + digit.val ≤ U8.max then
            scan radix.val U8.max false true
              ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
              (radix.val * value'.val + digit.val) (cursor'.val+1)
          else .overflow cursor'.val := by
          simp only [scanU8, List.drop_eq_getElem_cons hn, List.map_cons, scan]
          rw [← hd]
          simp [hbound]
        step as ⟨r8, hr8⟩
        have hr8val : r8.val = radix.val := by
          rw [hr8]
          have h := UScalar.cast_inBounds_spec .U8 radix (by simp only [UScalar.max_UScalarTy_U8_eq, u8_max_255]; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        have hcastval : (UScalar.cast .U8 digit).val = digit.val := by
          have h := UScalar.cast_inBounds_spec .U8 digit (by simp only [UScalar.max_UScalarTy_U8_eq, u8_max_255]; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        step as ⟨mul, hmul⟩
        cases mul with
        | none =>
          step as ⟨idx, hidx⟩
          change U8.max < value'.val * r8.val at hmul
          rw [u8_max_255, hr8val, Nat.mul_comm value'.val radix.val] at hmul
          have hbad : ¬(radix.val * value'.val + digit.val ≤ U8.max) := by
            rw [u8_max_255]; omega
          rw [←htarget, hscan, if_neg hbad]
          simp [agreesU8]
          omega
        | some product =>
          have hadd := U8.checked_add_bv_spec product (UScalar.cast .U8 digit)
          change value'.val * r8.val ≤ U8.max ∧ product.val = value'.val * r8.val ∧ _ at hmul
          rw [hr8val, u8_max_255, Nat.mul_comm value'.val radix.val] at hmul
          cases headd : U8.checked_add product (UScalar.cast .U8 digit) with
          | none =>
            simp only [headd] at hadd
            change U8.max < product.val + (UScalar.cast .U8 digit).val at hadd
            rw [u8_max_255] at hadd
            rw [hcastval] at hadd
            simp only [Std.lift, bind_ok, headd]
            step as ⟨idx, hidx⟩
            have hbad : ¬(radix.val * value'.val + digit.val ≤ U8.max) := by
              rw [u8_max_255]; omega
            rw [←htarget, hscan, if_neg hbad]
            simp [agreesU8]
            omega
          | some sum =>
            simp only [headd] at hadd
            rw [u8_max_255, hcastval] at hadd
            simp only [Std.lift, bind_ok, headd, WP.spec_ok]
            refine ⟨?_, by omega⟩
            dsimp [invU8]
            refine ⟨by omega, by omega, ?_⟩
            have hgood : radix.val * value'.val + digit.val ≤ U8.max := by
              rw [u8_max_255]; omega
            rw [←htarget, hscan, if_pos hgood]
            simp only [scanU8, hcursor]
            rw [hadd.2.1, hmul.2.1]
    · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none, it') := by
        simp [core.slice.iter.IteratorSliceIter.next, hn]
      rw [heq]
      simp only [bind_ok, WP.spec_ok]
      rw [←htarget]
      simp [scanU8, scan, agreesU8, List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
  · exact ⟨hi, hsafe, rfl⟩
unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun v _ hp => ⟨v, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem checked_u8_partial_spec (bytes : Slice U8) (value : U8) (cursor : Usize) (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (hsafe : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, partial.checked_u8_partial bytes value cursor radix = .ok out ∧
      agreesU8 out (scan radix.val U8.max false true
        (bytes.val.map UScalar.val) value.val cursor.val) := by
  apply result_spec_success
  unfold partial.checked_u8_partial
  simp only [core.slice.Slice.iter, bind_ok]
  have h := partial.checked_u8_partial_loop_spec radix hr ⟨bytes, 0⟩ value cursor
    (by simp) (by simpa using hsafe)
  simpa only [scanU8, List.drop_zero] using h

end GenericPartialU8Trial
