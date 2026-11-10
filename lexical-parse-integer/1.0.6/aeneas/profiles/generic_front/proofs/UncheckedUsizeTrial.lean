import GenericUsizeTrial
import GenericComposition
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition GenericUsizeTrial
namespace UncheckedUsizeTrial
private theorem usize_ge36 : 36≤Usize.max := by
 rcases Usize.bounds_eq with h|h
 · rw [h,U32.max_eq]; omega
 · rw [h,U64.max_eq]; omega
private theorem usize_size : UScalar.size .Usize=Usize.max+1 := by
 simp [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits,Usize.size]

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
theorem unchecked_usize_loop_spec (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36)
    (it : core.slice.iter.Iter U8) (value : Usize) (cursor : Usize)
    (hi : it.i ≤ it.slice.val.length)
    (hbudget : uncheckedBound radix.val Usize.max value.val (it.slice.val.length-it.i))
    (hsafe : cursor.val + (it.slice.val.length - it.i) ≤ Usize.max) :
    unchecked_usize_loop it value cursor radix
      ⦃ out => agreesUsize out (scanUsize radix it value cursor) ⦄ := by
  unfold unchecked_usize_loop
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.Iter U8 × Usize × Usize) => x.1.slice.val.length - x.1.i)
    (inv := fun x => invUsize radix (scanUsize radix it value cursor) x ∧ uncheckedBound radix.val Usize.max x.2.1.val (x.1.slice.val.length-x.1.i))
  · intro x hx
    rcases x with ⟨it', value', cursor'⟩
    obtain ⟨hx,hbudget'⟩ := hx
    dsimp [invUsize] at hx
    obtain ⟨hi', hsafe', htarget⟩ := hx
    dsimp only
    unfold unchecked_usize_loop.body
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
            scan radix.val Usize.max false false
              ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
              (radix.val * value'.val + digit.val) (cursor'.val+1)
          else .overflow cursor'.val := by
          simp only [scanUsize, List.drop_eq_getElem_cons hn, List.map_cons, scan]
          rw [← hd]
          simp [hbound]
        step as ⟨r8, hr8⟩
        have hr8val : r8.val = radix.val := by
          rw [hr8]
          have h := UScalar.cast_inBounds_spec .Usize radix (by simp only [UScalar.max_USize_eq]; have h:=usize_ge36; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        have hcastval : (UScalar.cast .Usize digit).val = digit.val := by
          have h := UScalar.cast_inBounds_spec .Usize digit (by simp only [UScalar.max_USize_eq]; have h:=usize_ge36; omega)
          simpa only [Std.lift, WP.spec_ok] using h
        have hcount : it'.slice.val.length-it'.i = (it'.slice.val.length-(it'.i+1))+1 := by omega
        rw [hcount] at hbudget'
        have hb := unchecked_bound_step radix.val Usize.max value'.val (it'.slice.val.length-(it'.i+1)) digit.val hr.1 hbound hbudget'
        have hnext := unchecked_bound_value radix.val Usize.max (radix.val*value'.val+digit.val) (it'.slice.val.length-(it'.i+1)) hr.1 hb
        let sum := core.num.Usize.wrapping_add (core.num.Usize.wrapping_mul value' r8) (UScalar.cast .Usize digit)
        have hsum : sum.val=radix.val*value'.val+digit.val := by
          simp only [sum,core.num.Usize.wrapping_add_val_eq,core.num.Usize.wrapping_mul_val_eq,UScalar.ofNatCore_val_eq,hr8val,hcastval]
          have hm : value'.val*radix.val < UScalar.size .Usize := by rw [usize_size,Nat.mul_comm value'.val radix.val]; omega
          rw [Nat.mod_eq_of_lt hm,Nat.mod_eq_of_lt (by rw [usize_size,Nat.mul_comm value'.val radix.val]; omega)]
          rw [Nat.mul_comm]
        simp only [Std.lift,bind_ok,WP.spec_ok]
        change invUsize radix (scanUsize radix it value cursor) ({it' with i:=it'.i+1},sum,cursor1) ∧
          uncheckedBound radix.val Usize.max sum.val (it'.slice.val.length-(it'.i+1)) ∧
          it'.slice.val.length-(it'.i+1) < it'.slice.val.length-it'.i
        refine ⟨?_,?_,by omega⟩
        · dsimp only [invUsize]
          refine ⟨by omega,by omega,?_⟩
          rw [←htarget,hscan,if_pos hnext]
          simp only [scanUsize,hcursor,hsum]
        · simpa only [hsum] using hb
    · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
        simp [core.slice.iter.IteratorSliceIter.next,hn]
      rw [heq]
      simp only [bind_ok,WP.spec_ok]
      rw [←htarget]
      simp [scanUsize,scan,agreesUsize,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
  · exact ⟨⟨hi,hsafe,rfl⟩,hbudget⟩
theorem unchecked_usize_spec (radix : U32) (hr : 2≤radix.val ∧ radix.val≤36)
 (bytes : Slice U8) (value : Usize) (cursor : Usize)
 (hbudget : uncheckedBound radix.val Usize.max value.val bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, unchecked_usize bytes value cursor radix = .ok out ∧
 agreesUsize out (scan radix.val Usize.max false false (bytes.val.map UScalar.val) value.val cursor.val) := by
 apply result_spec_success
 unfold unchecked_usize
 simp only [core.slice.Slice.iter,bind_ok]
 have h := unchecked_usize_loop_spec radix hr ⟨bytes,0⟩ value cursor (by simp) (by simpa using hbudget) (by simpa using hsafe)
 simpa only [scanUsize,List.drop_zero] using h
#print axioms unchecked_usize_spec
end UncheckedUsizeTrial
