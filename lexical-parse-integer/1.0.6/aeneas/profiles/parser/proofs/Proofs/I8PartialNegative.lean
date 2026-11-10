import Proofs.I8UncheckedPositive
import Proofs.SignedPartialObservation
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def scanPartial8Negative (it : core.slice.iter.Iter U8) (value : I8) (cursor : Usize) :=
 signedPartialScan 128 true ((it.slice.val.drop it.i).map UScalar.val) (mag8Negative value) cursor.val


def invPartial8Negative (target : SignedPartialResult) (x : core.slice.iter.Iter U8 × I8 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧ x.2.1.val≤0 ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scanPartial8Negative x.1 x.2.1 x.2.2=target

theorem partial_checked_negative8_loop_spec (it : core.slice.iter.Iter U8) (value : I8) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : value.val≤0)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 checked_i8_negative_partial_from_loop it value cursor ⦃ out => agreesSignedPartial out (scanPartial8Negative it value cursor) ⦄ := by
 unfold checked_i8_negative_partial_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I8 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := invPartial8Negative (scanPartial8Negative it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [invPartial8Negative] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmag : (mag8Negative value' : Int) = -value'.val := by simp [mag8Negative,Int.toNat_of_nonneg (by omega : 0≤ -value'.val)]
   dsimp only
   unfold checked_i8_negative_partial_from_loop.body
   by_cases hn : it'.i < it'.slice.val.length
   · have heq : core.slice.iter.IteratorSliceIter.next it' =
       .ok (some it'.slice.val[it'.i],{it' with i:=it'.i+1}) := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]; rfl
     rw [heq]
     simp only [bind_ok]
     step as ⟨cursor1,hcursor⟩
     step as ⟨d,hd⟩
     cases d with
     | none =>
       step as ⟨idx,hidx⟩
       rw [←htarget]
       simp only [scanPartial8Negative,List.drop_eq_getElem_cons hn,List.map_cons,signedPartialScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agreesSignedPartial,signedValue]
       try simp only [Int.ofNat_eq_natCast,ite_true,Bool.false_eq_true,ite_false]
       omega
     | some digit =>
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hcast : (UScalar.hcast .I8 digit).val = digit.val := by
         have h := UScalar.hcast_inBounds_spec .I8 digit (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hscan : scanPartial8Negative it' value' cursor' =
         if 10*mag8Negative value'+digit.val ≤ 128 then
           signedPartialScan 128 true ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*mag8Negative value'+digit.val) (cursor'.val+1)
         else .underflow cursor'.val := by
         simp only [scanPartial8Negative,List.drop_eq_getElem_cons hn,List.map_cons,
           signedPartialScan,decimalDigit,if_pos hvalid,←hd.2.2]
         simp
       simp only [show UScalar.hcast .I8 10#u32 = 10#i8 by rfl,Std.lift,bind_ok]
       have hmul := I8.checked_mul_bv_spec value' 10#i8
       change (match I8.checked_mul value' 10#i8 with
         | some z => I8.min≤value'.val*10 ∧ value'.val*10≤I8.max ∧
             z.val=value'.val*10 ∧ z.bv=value'.bv*10#8
         | none => ¬(I8.min≤value'.val*10 ∧ value'.val*10≤I8.max)) at hmul
       cases hemul : I8.checked_mul value' 10#i8 with
       | none =>
         try simp only [hemul] at hmul
         try simp only [hemul,bind_ok]
         step as ⟨idx,hidx⟩
         try dsimp only at hmul
         rw [←htarget,hscan,if_neg (by simp only [I8.min_eq,I8.max_eq] at hmul; omega)]
         dsimp only [agreesSignedPartial,signedValue]
         try simp only [Int.ofNat_eq_natCast,ite_true,Bool.false_eq_true,ite_false]
         omega
       | some product =>
         try simp only [hemul] at hmul
         try simp only [hemul,Std.lift,bind_ok]
         try dsimp only at hmul
         have hadd := I8.checked_sub_bv_spec product (UScalar.hcast .I8 digit)
         change (match I8.checked_sub product (UScalar.hcast .I8 digit) with
           | some z => I8.min≤product.val-(UScalar.hcast .I8 digit).val ∧
               product.val-(UScalar.hcast .I8 digit).val≤I8.max ∧
               z.val=product.val-(UScalar.hcast .I8 digit).val ∧
               z.bv=product.bv-I8.bv (UScalar.hcast .I8 digit)
           | none => ¬(I8.min≤product.val-(UScalar.hcast .I8 digit).val ∧
               product.val-(UScalar.hcast .I8 digit).val≤I8.max)) at hadd
         cases headd : I8.checked_sub product (UScalar.hcast .I8 digit) with
         | none =>
           try simp only [headd] at hadd
           try simp only [headd]
           step as ⟨idx,hidx⟩
           rw [←htarget,hscan,if_neg (by simp only [I8.min_eq,I8.max_eq] at hadd; omega)]
           dsimp only [agreesSignedPartial,signedValue]
           try simp only [Int.ofNat_eq_natCast,ite_true,Bool.false_eq_true,ite_false]
           omega
         | some sum =>
           try simp only [headd] at hadd
           simp only [headd,WP.spec_ok]
           refine ⟨?_,by omega⟩
           dsimp only [invPartial8Negative]
           have hsum : sum.val = value'.val*10-digit.val := by omega
           have hnonpos : sum.val≤0 := by omega
           refine ⟨by omega,hnonpos,by omega,?_⟩
           rw [←htarget,hscan,if_pos (by simp only [I8.min_eq,I8.max_eq] at hadd; omega)]
           simp only [scanPartial8Negative,hcursor]
           rw [show mag8Negative sum = 10*mag8Negative value'+digit.val by dsimp [mag8Negative]; omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scanPartial8Negative,signedPartialScan,agreesSignedPartial,signedValue,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨hi,hv,hsafe,rfl⟩

theorem checked_i8_negative_partial_from_spec (bytes : Slice U8) (value : I8) (cursor : Usize)
 (hv : value.val≤0) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, checked_i8_negative_partial_from bytes value cursor = .ok out ∧
   agreesSignedPartial out (signedPartialScan 128 true (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) := by
 apply result_spec_success
 unfold checked_i8_negative_partial_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := partial_checked_negative8_loop_spec ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hsafe)
 simpa only [scanPartial8Negative,List.drop_zero] using h

end LexicalScalarProofs
