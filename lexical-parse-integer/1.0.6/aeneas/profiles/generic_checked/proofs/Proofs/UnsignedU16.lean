import Proofs.Digit
import GenericScalarSpecs
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_harness
namespace LexicalGenericU16Proofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
open LexicalParseIntegerGenericSpec

private theorem u16_max_65535 : U16.max = 65535 := U16.max_eq

def agreesU16 (r : core.result.Result U16 lexical_util.error.Error) : ScanResult → Prop
  | .value n _ => match r with | .Ok x => x.val = n | _ => False
  | .invalidDigit i => match r with | .Err (.InvalidDigit j) => j.val = i | _ => False
  | .overflow i => match r with | .Err (.Overflow j) => j.val = i | _ => False
  | .underflow _ => False

def scanU16 (radix : U32) (it : core.slice.iter.Iter U8) (value : U16) (cursor : Usize) : ScanResult :=
  scan radix.val U16.max false false ((it.slice.val.drop it.i).map UScalar.val) value.val cursor.val

def invU16 (radix : U32) (target : ScanResult)
    (x : core.slice.iter.Iter U8 × U16 × Usize) : Prop :=
  x.1.i ≤ x.1.slice.val.length ∧
  x.2.2.val + (x.1.slice.val.length - x.1.i) ≤ Usize.max ∧
  scanU16 radix x.1 x.2.1 x.2.2 = target

theorem checked_u16_loop_spec (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (it : core.slice.iter.Iter U8) (value : U16) (cursor : Usize)
    (hi : it.i ≤ it.slice.val.length)
    (hsafe : cursor.val + (it.slice.val.length - it.i) ≤ Usize.max) :
    checked_u16_loop it value cursor radix
      ⦃ out => agreesU16 out (scanU16 radix it value cursor) ⦄ := by
  unfold checked_u16_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.Iter U8 × U16 × Usize) => x.1.slice.val.length - x.1.i)
    (inv := invU16 radix (scanU16 radix it value cursor))
  · intro x hx
    rcases x with ⟨it', value', cursor'⟩
    dsimp [invU16] at hx
    obtain ⟨hi', hsafe', htarget⟩ := hx
    dsimp only
    unfold checked_u16_loop.body
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
        simp only [scanU16, List.drop_eq_getElem_cons hn, List.map_cons, scan]
        simp only [Option.map_none] at hd
        rw [←hd]
        simp [agreesU16]
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
        have hscan : scanU16 radix it' value' cursor' =
          if radix.val * value'.val + digit.val ≤ U16.max then
            scan radix.val U16.max false false
              ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
              (radix.val * value'.val + digit.val) (cursor'.val+1)
          else .overflow cursor'.val := by
          simp only [scanU16, List.drop_eq_getElem_cons hn, List.map_cons, scan]
          rw [← hd]
          simp [hbound]
        step as ⟨r8, hr8⟩
        have hr8val : r8.val = radix.val := by
          rw [hr8]
          have h := UScalar.cast_inBounds_spec .U16 radix (by simp only [UScalar.max_UScalarTy_U16_eq, u16_max_65535]; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        have hcastval : (UScalar.cast .U16 digit).val = digit.val := by
          have h := UScalar.cast_inBounds_spec .U16 digit (by simp only [UScalar.max_UScalarTy_U16_eq, u16_max_65535]; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        step as ⟨mul, hmul⟩
        cases mul with
        | none =>
          step as ⟨idx, hidx⟩
          change U16.max < value'.val * r8.val at hmul
          rw [u16_max_65535, hr8val, Nat.mul_comm value'.val radix.val] at hmul
          have hbad : ¬(radix.val * value'.val + digit.val ≤ U16.max) := by
            rw [u16_max_65535]; omega
          rw [←htarget, hscan, if_neg hbad]
          simp [agreesU16]
          omega
        | some product =>
          have hadd := U16.checked_add_bv_spec product (UScalar.cast .U16 digit)
          change value'.val * r8.val ≤ U16.max ∧ product.val = value'.val * r8.val ∧ _ at hmul
          rw [hr8val, u16_max_65535, Nat.mul_comm value'.val radix.val] at hmul
          cases headd : U16.checked_add product (UScalar.cast .U16 digit) with
          | none =>
            simp only [headd] at hadd
            change U16.max < product.val + (UScalar.cast .U16 digit).val at hadd
            rw [u16_max_65535] at hadd
            rw [hcastval] at hadd
            simp only [Std.lift, bind_ok, headd]
            step as ⟨idx, hidx⟩
            have hbad : ¬(radix.val * value'.val + digit.val ≤ U16.max) := by
              rw [u16_max_65535]; omega
            rw [←htarget, hscan, if_neg hbad]
            simp [agreesU16]
            omega
          | some sum =>
            simp only [headd] at hadd
            rw [u16_max_65535, hcastval] at hadd
            simp only [Std.lift, bind_ok, headd, WP.spec_ok]
            refine ⟨?_, by omega⟩
            dsimp [invU16]
            refine ⟨by omega, by omega, ?_⟩
            have hgood : radix.val * value'.val + digit.val ≤ U16.max := by
              rw [u16_max_65535]; omega
            rw [←htarget, hscan, if_pos hgood]
            simp only [scanU16, hcursor]
            rw [hadd.2.1, hmul.2.1]
    · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none, it') := by
        simp [core.slice.iter.IteratorSliceIter.next, hn]
      rw [heq]
      simp only [bind_ok, WP.spec_ok]
      rw [←htarget]
      simp [scanU16, scan, agreesU16, List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
  · exact ⟨hi, hsafe, rfl⟩
unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun v _ hp => ⟨v, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem checked_u16_spec (bytes : Slice U8) (value : U16) (cursor : Usize) (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (hsafe : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, checked_u16 bytes value cursor radix = .ok out ∧
      agreesU16 out (scan radix.val U16.max false false
        (bytes.val.map UScalar.val) value.val cursor.val) := by
  apply result_spec_success
  unfold checked_u16
  simp only [core.slice.Slice.iter, bind_ok]
  have h := checked_u16_loop_spec radix hr ⟨bytes, 0⟩ value cursor
    (by simp) (by simpa using hsafe)
  simpa only [scanU16, List.drop_zero] using h

end LexicalGenericU16Proofs
