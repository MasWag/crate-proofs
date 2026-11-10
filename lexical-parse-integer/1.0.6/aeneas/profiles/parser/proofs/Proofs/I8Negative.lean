import Proofs.Scalar
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def mag8Negative (value : I8) : Nat := (-value.val).toNat

def scan8Negative (it : core.slice.iter.Iter U8) (value : I8) (cursor : Usize) :=
 boundedScan 128 true ((it.slice.val.drop it.i).map UScalar.val) (mag8Negative value) cursor.val

def agrees8Negative (r : core.result.Result I8 lexical_util.error.Error) : ScanResult → Prop
 | .value v => match r with | .Ok x => x.val = -(v : Int) | _ => False
 | .invalidDigit i => match r with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .underflow i => match r with | .Err (.Underflow j) => j.val=i | _ => False
 | .overflow _ => False

def inv8Negative (target : ScanResult) (x : core.slice.iter.Iter U8 × I8 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧ x.2.1.val≤0 ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scan8Negative x.1 x.2.1 x.2.2=target

theorem checked_negative8_loop_spec (it : core.slice.iter.Iter U8) (value : I8) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : value.val≤0)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 checked_i8_negative_from_loop it value cursor ⦃ out => agrees8Negative out (scan8Negative it value cursor) ⦄ := by
 unfold checked_i8_negative_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I8 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := inv8Negative (scan8Negative it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [inv8Negative] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmag : (mag8Negative value' : Int) = -value'.val := by simp [mag8Negative,Int.toNat_of_nonneg (by omega : 0≤ -value'.val)]
   dsimp only
   unfold checked_i8_negative_from_loop.body
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
       simp only [scan8Negative,List.drop_eq_getElem_cons hn,List.map_cons,boundedScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agrees8Negative]
       omega
     | some digit =>
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hcast : (UScalar.hcast .I8 digit).val = digit.val := by
         have h := UScalar.hcast_inBounds_spec .I8 digit (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hscan : scan8Negative it' value' cursor' =
         if 10*mag8Negative value'+digit.val ≤ 128 then
           boundedScan 128 true ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*mag8Negative value'+digit.val) (cursor'.val+1)
         else .underflow cursor'.val := by
         simp only [scan8Negative,List.drop_eq_getElem_cons hn,List.map_cons,
           boundedScan,decimalDigit,if_pos hvalid,←hd.2.2]
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
         dsimp only [agrees8Negative]
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
           dsimp only [agrees8Negative]
           omega
         | some sum =>
           try simp only [headd] at hadd
           simp only [headd,WP.spec_ok]
           refine ⟨?_,by omega⟩
           dsimp only [inv8Negative]
           have hsum : sum.val = value'.val*10-digit.val := by omega
           have hnonpos : sum.val≤0 := by omega
           refine ⟨by omega,hnonpos,by omega,?_⟩
           rw [←htarget,hscan,if_pos (by simp only [I8.min_eq,I8.max_eq] at hadd; omega)]
           simp only [scan8Negative,hcursor]
           rw [show mag8Negative sum = 10*mag8Negative value'+digit.val by dsimp [mag8Negative]; omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scan8Negative,boundedScan,agrees8Negative,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨hi,hv,hsafe,rfl⟩

theorem checked_i8_negative_from_spec (bytes : Slice U8) (value : I8) (cursor : Usize)
 (hv : value.val≤0) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, checked_i8_negative_from bytes value cursor = .ok out ∧
   agrees8Negative out (boundedScan 128 true (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) := by
 apply result_spec_success
 unfold checked_i8_negative_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := checked_negative8_loop_spec ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hsafe)
 simpa only [scan8Negative,List.drop_zero] using h

end LexicalScalarProofs