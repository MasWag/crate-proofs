import SignedI16Neg
import GenericComposition
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition LexicalGenericI16NegProofs
namespace SignedUncheckedI16Neg
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
theorem unchecked_negative16_loop_spec (radix : U32) (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) (it : core.slice.iter.Iter U8) (value : I16) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : value.val≤0)
 (hbudget : uncheckedBound radix.val 32768 (mag8Negative value) (it.slice.val.length-it.i))
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 unchecked_i16_negative_loop it value cursor radix ⦃ out => agrees8Negative out (scan8Negative radix it value cursor) ⦄ := by
 unfold unchecked_i16_negative_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I16 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := fun x => inv8Negative radix (scan8Negative radix it value cursor) x ∧ uncheckedBound radix.val 32768 (mag8Negative x.2.1) (x.1.slice.val.length-x.1.i))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   obtain ⟨hx,hbudget'⟩ := hx
   dsimp [inv8Negative] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmagNeg : (mag8Negative value' : Int) = -value'.val := by simp [mag8Negative,Int.toNat_of_nonneg (by omega : 0≤ -value'.val)]
   dsimp only
   unfold unchecked_i16_negative_loop.body
   by_cases hn : it'.i < it'.slice.val.length
   · have heq : core.slice.iter.IteratorSliceIter.next it' =
       .ok (some it'.slice.val[it'.i],{it' with i:=it'.i+1}) := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]; rfl
     rw [heq]
     simp only [bind_ok]
     step as ⟨cursor1,hcursor⟩
     obtain ⟨d, hdcall, hd⟩ := LexicalDigitProofs.char_to_digit_const_spec
       it'.slice.val[it'.i] radix hr
     rw [hdcall]
     simp only [bind_ok]
     cases d with
     | none =>
       step as ⟨idx,hidx⟩
       rw [←htarget]
       simp only [scan8Negative,List.drop_eq_getElem_cons hn,List.map_cons,scan]
       simp only [Option.map_none] at hd
       rw [←hd]
       dsimp only [agrees8Negative]
       simp only [Bool.false_eq_true, ite_false]
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
       have hcast : (UScalar.hcast .I16 digit).val = digit.val := by
         have h := UScalar.hcast_inBounds_spec .I16 digit (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hscan : scan8Negative radix it' value' cursor' =
         if radix.val*mag8Negative value'+digit.val ≤ 32768 then
           scan radix.val 32768 true false ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (radix.val*mag8Negative value'+digit.val) (cursor'.val+1)
         else .underflow cursor'.val := by
         simp only [scan8Negative,List.drop_eq_getElem_cons hn,List.map_cons,
           scan,←hd]
         simp
       step as ⟨radix8, hradix8⟩
       have hradixval : radix8.val = radix.val := by
         rw [hradix8]
         have h := UScalar.hcast_inBounds_spec .I16 radix (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hterm : (↑(radix.val * mag8Negative value') : Int) = -(value'.val * radix8.val) := by
         simp [Nat.cast_mul, hmagNeg, hradixval, mul_comm]
       have hprodNonpos : value'.val * radix8.val ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv' (by omega)
       have hcount : it'.slice.val.length-it'.i=(it'.slice.val.length-(it'.i+1))+1 := by omega
       rw [hcount] at hbudget'
       have hb := unchecked_bound_step radix.val 32768 (mag8Negative value') (it'.slice.val.length-(it'.i+1)) digit.val hr.1 hbound hbudget'
       have hnext := unchecked_bound_value radix.val 32768 (radix.val*mag8Negative value'+digit.val) (it'.slice.val.length-(it'.i+1)) hr.1 hb
       let product:=core.num.I16.wrapping_mul value' radix8
       have hproduct : product.val=value'.val*radix8.val := by
         simp only [product,core.num.I16.wrapping_mul_val_eq]
         apply Int.bmod_eq_of_le <;> omega
       let sum:=core.num.I16.wrapping_sub product (UScalar.hcast .I16 digit)
       have hsum : sum.val= -((radix.val*mag8Negative value'+digit.val:Nat):Int) := by
         simp only [sum,core.num.I16.wrapping_sub_val_eq,hproduct,hcast]
         rw [Int.bmod_eq_of_le (by omega) (by omega)]
         simp only [Nat.cast_add,hterm]
         omega
       simp only [Std.lift,bind_ok,WP.spec_ok]
       change inv8Negative radix (scan8Negative radix it value cursor) ({it' with i:=it'.i+1},sum,cursor1) ∧
         uncheckedBound radix.val 32768 (mag8Negative sum) (it'.slice.val.length-(it'.i+1)) ∧
         it'.slice.val.length-(it'.i+1) < it'.slice.val.length-it'.i
       have hmagSum : mag8Negative sum=radix.val*mag8Negative value'+digit.val := by
         change (-sum.val).toNat=radix.val*mag8Negative value'+digit.val
         rw [hsum]
         simp only [Int.neg_neg,Int.toNat_natCast]
       refine ⟨?_,by simpa only [hmagSum] using hb,by omega⟩
       dsimp only [inv8Negative]
       refine ⟨by omega,by omega,by omega,?_⟩
       rw [←htarget,hscan,if_pos hnext]
       simp only [scan8Negative,hcursor,hmagSum]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scan8Negative,scan,agrees8Negative,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨⟨hi,hv,hsafe,rfl⟩,hbudget⟩
theorem unchecked_i16_negative_spec (radix : U32) (hr : 2≤radix.val ∧ radix.val≤36)
 (bytes : Slice U8) (value : I16) (cursor : Usize) (hv : value.val≤0)
 (hb : uncheckedBound radix.val 32768 (mag8Negative value) bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, unchecked_i16_negative bytes value cursor radix=.ok out ∧
 agrees8Negative out (scan radix.val 32768 true false (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) := by
 apply result_spec_success
 unfold unchecked_i16_negative
 simp only [core.slice.Slice.iter,bind_ok]
 have h:=unchecked_negative16_loop_spec radix hr ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hb) (by simpa using hsafe)
 simpa only [scan8Negative,List.drop_zero] using h
#print axioms unchecked_i16_negative_spec
end SignedUncheckedI16Neg
