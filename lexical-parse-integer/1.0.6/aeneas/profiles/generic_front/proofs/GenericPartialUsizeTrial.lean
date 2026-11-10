import GenericDigit
import GenericScalarSpecs
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness
open lexical_parse_integer_generic_harness
namespace GenericPartialUsizeTrial
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
open LexicalParseIntegerGenericSpec

private theorem usize_max_ge_36 : 36 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h
  · rw [h, U32.max_eq]; omega
  · rw [h, U64.max_eq]; omega

def agreesUsize (r : core.result.Result (Usize × Usize) lexical_util.error.Error) : ScanResult → Prop
  | .value n consumed => match r with | .Ok x => x.1.val = n ∧ x.2.val = consumed | _ => False
  | .invalidDigit _ => False
  | .overflow i => match r with | .Err (.Overflow j) => j.val = i | _ => False
  | .underflow _ => False

def scanUsize (radix : U32) (it : core.slice.iter.Iter U8) (value : Usize) (cursor : Usize) : ScanResult :=
  scan radix.val Usize.max false true ((it.slice.val.drop it.i).map UScalar.val) value.val cursor.val

def invUsize (radix : U32) (target : ScanResult)
    (x : core.slice.iter.Iter U8 × Usize × Usize) : Prop :=
  x.1.i ≤ x.1.slice.val.length ∧
  x.2.2.val + (x.1.slice.val.length - x.1.i) ≤ Usize.max ∧
  scanUsize radix x.1 x.2.1 x.2.2 = target

theorem partial.checked_usize_partial_loop_spec (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (it : core.slice.iter.Iter U8) (value : Usize) (cursor : Usize)
    (hi : it.i ≤ it.slice.val.length)
    (hsafe : cursor.val + (it.slice.val.length - it.i) ≤ Usize.max) :
    partial.checked_usize_partial_loop it value cursor radix
      ⦃ out => agreesUsize out (scanUsize radix it value cursor) ⦄ := by
  unfold partial.checked_usize_partial_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.Iter U8 × Usize × Usize) => x.1.slice.val.length - x.1.i)
    (inv := invUsize radix (scanUsize radix it value cursor))
  · intro x hx
    rcases x with ⟨it', value', cursor'⟩
    dsimp [invUsize] at hx
    obtain ⟨hi', hsafe', htarget⟩ := hx
    dsimp only
    unfold partial.checked_usize_partial_loop.body
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
        simp only [scanUsize, List.drop_eq_getElem_cons hn, List.map_cons, scan]
        simp only [Option.map_none] at hd
        rw [←hd]
        simp [agreesUsize]
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
        have hscan : scanUsize radix it' value' cursor' =
          if radix.val * value'.val + digit.val ≤ Usize.max then
            scan radix.val Usize.max false true
              ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
              (radix.val * value'.val + digit.val) (cursor'.val+1)
          else .overflow cursor'.val := by
          simp only [scanUsize, List.drop_eq_getElem_cons hn, List.map_cons, scan]
          rw [← hd]
          simp [hbound]
        have hmax := usize_max_ge_36
        step as ⟨r8, hr8⟩
        have hr8val : r8.val = radix.val := by
          rw [hr8]
          have h := UScalar.cast_inBounds_spec .Usize radix (by simp only [UScalar.max_USize_eq]; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        have hcastval : (UScalar.cast .Usize digit).val = digit.val := by
          have h := UScalar.cast_inBounds_spec .Usize digit (by simp only [UScalar.max_USize_eq]; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        step as ⟨mul, hmul⟩
        cases mul with
        | none =>
          step as ⟨idx, hidx⟩
          change Usize.max < value'.val * r8.val at hmul
          rw [hr8val, Nat.mul_comm value'.val radix.val] at hmul
          have hbad : ¬(radix.val * value'.val + digit.val ≤ Usize.max) := by
            omega
          rw [←htarget, hscan, if_neg hbad]
          simp [agreesUsize]
          omega
        | some product =>
          have hadd := Usize.checked_add_bv_spec product (UScalar.cast .Usize digit)
          change value'.val * r8.val ≤ Usize.max ∧ product.val = value'.val * r8.val ∧ _ at hmul
          rw [hr8val, Nat.mul_comm value'.val radix.val] at hmul
          cases headd : Usize.checked_add product (UScalar.cast .Usize digit) with
          | none =>
            simp only [headd] at hadd
            change Usize.max < product.val + (UScalar.cast .Usize digit).val at hadd
            rw [hcastval] at hadd
            simp only [Std.lift, bind_ok, headd]
            step as ⟨idx, hidx⟩
            have hbad : ¬(radix.val * value'.val + digit.val ≤ Usize.max) := by
              omega
            rw [←htarget, hscan, if_neg hbad]
            simp [agreesUsize]
            omega
          | some sum =>
            simp only [headd] at hadd
            rw [hcastval] at hadd
            simp only [Std.lift, bind_ok, headd, WP.spec_ok]
            refine ⟨?_, by omega⟩
            dsimp [invUsize]
            refine ⟨by omega, by omega, ?_⟩
            have hgood : radix.val * value'.val + digit.val ≤ Usize.max := by
              omega
            rw [←htarget, hscan, if_pos hgood]
            simp only [scanUsize, hcursor]
            rw [hadd.2.1, hmul.2.1]
    · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none, it') := by
        simp [core.slice.iter.IteratorSliceIter.next, hn]
      rw [heq]
      simp only [bind_ok, WP.spec_ok]
      rw [←htarget]
      simp [scanUsize, scan, agreesUsize, List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
  · exact ⟨hi, hsafe, rfl⟩
unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun v _ hp => ⟨v, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem checked_usize_partial_spec (bytes : Slice U8) (value : Usize) (cursor : Usize) (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (hsafe : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, partial.checked_usize_partial bytes value cursor radix = .ok out ∧
      agreesUsize out (scan radix.val Usize.max false true
        (bytes.val.map UScalar.val) value.val cursor.val) := by
  apply result_spec_success
  unfold partial.checked_usize_partial
  simp only [core.slice.Slice.iter, bind_ok]
  have h := partial.checked_usize_partial_loop_spec radix hr ⟨bytes, 0⟩ value cursor
    (by simp) (by simpa using hsafe)
  simpa only [scanUsize, List.drop_zero] using h

end GenericPartialUsizeTrial
