import SignedIsizePos
import GenericComposition
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition LexicalGenericIsizePosProofs
namespace SignedUncheckedIsizePos
private theorem isize_size64 (h : System.Platform.numBits=64) : Isize.size=18446744073709551616 := by simp [Isize.size,Isize.numBits,h]
private theorem isize_min64 (h : System.Platform.numBits=64) : Isize.min= -9223372036854775808 := by simp [Isize.min,Isize.numBits,h]
private theorem isize_max64 (h : System.Platform.numBits=64) : Isize.max=9223372036854775807 := by simp [Isize.max,Isize.numBits,h]

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
theorem unchecked_positive8_loop_spec (radix : U32) (hplat : System.Platform.numBits=64) (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) (it : core.slice.iter.Iter U8) (value : Isize) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : 0≤value.val)
 (hbudget : uncheckedBound radix.val 9223372036854775807 (mag8Positive value) (it.slice.val.length-it.i))
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 unchecked_isize_positive_loop it value cursor radix ⦃ out => agrees8Positive out (scan8Positive radix it value cursor) ⦄ := by
 unfold unchecked_isize_positive_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × Isize × Usize) => x.1.slice.val.length-x.1.i)
   (inv := fun x => inv8Positive radix (scan8Positive radix it value cursor) x ∧ uncheckedBound radix.val 9223372036854775807 (mag8Positive x.2.1) (x.1.slice.val.length-x.1.i))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   obtain ⟨hx,hbudget'⟩ := hx
   dsimp [inv8Positive] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmagPos : (mag8Positive value' : Int) = value'.val := by simp [mag8Positive,Int.toNat_of_nonneg (by omega : 0≤ value'.val)]
   dsimp only
   unfold unchecked_isize_positive_loop.body
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
       simp only [scan8Positive,List.drop_eq_getElem_cons hn,List.map_cons,scan]
       simp only [Option.map_none] at hd
       rw [←hd]
       dsimp only [agrees8Positive]
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
       have hcast : (UScalar.hcast .Isize digit).val = digit.val := by
         have h := UScalar.hcast_inBounds_spec .Isize digit (by simp only [IScalar.max,IScalarTy.numBits,hplat]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hscan : scan8Positive radix it' value' cursor' =
         if radix.val*mag8Positive value'+digit.val ≤ 9223372036854775807 then
           scan radix.val 9223372036854775807 false false ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (radix.val*mag8Positive value'+digit.val) (cursor'.val+1)
         else .overflow cursor'.val := by
         simp only [scan8Positive,List.drop_eq_getElem_cons hn,List.map_cons,
           scan,isize_min64 hplat,isize_max64 hplat,←hd]
         simp
       step as ⟨radix8, hradix8⟩
       have hradixval : radix8.val = radix.val := by
         rw [hradix8]
         have h := UScalar.hcast_inBounds_spec .Isize radix (by simp only [IScalar.max,IScalarTy.numBits,hplat]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hterm : (↑(radix.val * mag8Positive value') : Int) = value'.val * radix8.val := by
         simp [Nat.cast_mul, hmagPos, hradixval, mul_comm]
       have hprodNonneg : 0 ≤ value'.val * radix8.val := mul_nonneg hv' (by omega)
       have hcount : it'.slice.val.length-it'.i=(it'.slice.val.length-(it'.i+1))+1 := by omega
       rw [hcount] at hbudget'
       have hb := unchecked_bound_step radix.val 9223372036854775807 (mag8Positive value') (it'.slice.val.length-(it'.i+1)) digit.val hr.1 hbound hbudget'
       have hnext := unchecked_bound_value radix.val 9223372036854775807 (radix.val*mag8Positive value'+digit.val) (it'.slice.val.length-(it'.i+1)) hr.1 hb
       let product:=core.num.Isize.wrapping_mul value' radix8
       have hproduct : product.val=value'.val*radix8.val := by
         simp only [product,core.num.Isize.wrapping_mul_val_eq,isize_size64 hplat,hplat]
         norm_num only
         apply Int.bmod_eq_of_le <;> omega
       let sum:=core.num.Isize.wrapping_add product (UScalar.hcast .Isize digit)
       have hsum : sum.val= ((radix.val*mag8Positive value'+digit.val:Nat):Int) := by
         simp only [sum,core.num.Isize.wrapping_add_val_eq,isize_size64 hplat,hplat,hproduct,hcast]
         norm_num only
         rw [Int.bmod_eq_of_le (by omega) (by omega)]
         simp only [Nat.cast_add,hterm]
       simp only [Std.lift,bind_ok,WP.spec_ok]
       change inv8Positive radix (scan8Positive radix it value cursor) ({it' with i:=it'.i+1},sum,cursor1) ∧
         uncheckedBound radix.val 9223372036854775807 (mag8Positive sum) (it'.slice.val.length-(it'.i+1)) ∧
         it'.slice.val.length-(it'.i+1) < it'.slice.val.length-it'.i
       have hmagSum : mag8Positive sum=radix.val*mag8Positive value'+digit.val := by
         change sum.val.toNat=radix.val*mag8Positive value'+digit.val
         rw [hsum]
         simp only [Int.toNat_natCast]
       refine ⟨?_,by simpa only [hmagSum] using hb,by omega⟩
       dsimp only [inv8Positive]
       refine ⟨by omega,by omega,by omega,?_⟩
       rw [←htarget,hscan,if_pos hnext]
       simp [scan8Positive,hcursor,hmagSum,isize_max64 hplat]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scan8Positive,scan,agrees8Positive,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨⟨hi,hv,hsafe,rfl⟩,hbudget⟩
theorem unchecked_isize_positive_spec (radix : U32) (hplat : System.Platform.numBits=64) (hr : 2≤radix.val ∧ radix.val≤36)
 (bytes : Slice U8) (value : Isize) (cursor : Usize) (hv : 0≤value.val)
 (hb : uncheckedBound radix.val 9223372036854775807 (mag8Positive value) bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, unchecked_isize_positive bytes value cursor radix=.ok out ∧
 agrees8Positive out (scan radix.val 9223372036854775807 false false (bytes.val.map UScalar.val) (mag8Positive value) cursor.val) := by
 apply result_spec_success
 unfold unchecked_isize_positive
 simp only [core.slice.Slice.iter,bind_ok]
 have h:=unchecked_positive8_loop_spec radix hplat hr ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hb) (by simpa using hsafe)
 simpa [isize_min64 hplat,isize_max64 hplat,scan8Positive,List.drop_zero] using h
#print axioms unchecked_isize_positive_spec
end SignedUncheckedIsizePos
