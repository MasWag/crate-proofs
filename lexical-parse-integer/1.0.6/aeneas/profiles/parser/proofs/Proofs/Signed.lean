import Proofs.Scalar
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def mag (value : I32) : Nat := (-value.val).toNat

def scanNeg (it : core.slice.iter.Iter U8) (value : I32) (cursor : Usize) :=
 boundedScan 2147483648 true ((it.slice.val.drop it.i).map UScalar.val) (mag value) cursor.val

def agreesNeg (r : core.result.Result I32 lexical_util.error.Error) : ScanResult → Prop
 | .value v => match r with | .Ok x => x.val = -(v : Int) | _ => False
 | .invalidDigit i => match r with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .underflow i => match r with | .Err (.Underflow j) => j.val=i | _ => False
 | .overflow _ => False

def invNeg (target : ScanResult) (x : core.slice.iter.Iter U8 × I32 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧ x.2.1.val≤0 ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scanNeg x.1 x.2.1 x.2.2=target

theorem checked_negative_loop_spec (it : core.slice.iter.Iter U8) (value : I32) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : value.val≤0)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 checked_i32_negative_from_loop it value cursor ⦃ out => agreesNeg out (scanNeg it value cursor) ⦄ := by
 unfold checked_i32_negative_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I32 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := invNeg (scanNeg it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [invNeg] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmag : (mag value' : Int) = -value'.val := by simp [mag,Int.toNat_of_nonneg (by omega : 0≤ -value'.val)]
   dsimp only
   unfold checked_i32_negative_from_loop.body
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
       simp only [scanNeg,List.drop_eq_getElem_cons hn,List.map_cons,boundedScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agreesNeg]
       omega
     | some digit =>
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hcast : (UScalar.hcast .I32 digit).val = digit.val := by
         have h := UScalar.hcast_inBounds_spec .I32 digit (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hscan : scanNeg it' value' cursor' =
         if 10*mag value'+digit.val ≤ 2147483648 then
           boundedScan 2147483648 true ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*mag value'+digit.val) (cursor'.val+1)
         else .underflow cursor'.val := by
         simp only [scanNeg,List.drop_eq_getElem_cons hn,List.map_cons,
           boundedScan,decimalDigit,if_pos hvalid,←hd.2.2]
         simp
       simp only [show UScalar.hcast .I32 10#u32 = 10#i32 by rfl,Std.lift,bind_ok]
       have hmul := I32.checked_mul_bv_spec value' 10#i32
       change (match I32.checked_mul value' 10#i32 with
         | some z => I32.min≤value'.val*10 ∧ value'.val*10≤I32.max ∧
             z.val=value'.val*10 ∧ z.bv=value'.bv*10#32
         | none => ¬(I32.min≤value'.val*10 ∧ value'.val*10≤I32.max)) at hmul
       cases hemul : I32.checked_mul value' 10#i32 with
       | none =>
         try simp only [hemul] at hmul
         try simp only [hemul,bind_ok]
         step as ⟨idx,hidx⟩
         try dsimp only at hmul
         rw [←htarget,hscan,if_neg (by simp only [I32.min_eq,I32.max_eq] at hmul; omega)]
         dsimp only [agreesNeg]
         omega
       | some product =>
         try simp only [hemul] at hmul
         try simp only [hemul,Std.lift,bind_ok]
         try dsimp only at hmul
         have hadd := I32.checked_sub_bv_spec product (UScalar.hcast .I32 digit)
         change (match I32.checked_sub product (UScalar.hcast .I32 digit) with
           | some z => I32.min≤product.val-(UScalar.hcast .I32 digit).val ∧
               product.val-(UScalar.hcast .I32 digit).val≤I32.max ∧
               z.val=product.val-(UScalar.hcast .I32 digit).val ∧
               z.bv=product.bv-I32.bv (UScalar.hcast .I32 digit)
           | none => ¬(I32.min≤product.val-(UScalar.hcast .I32 digit).val ∧
               product.val-(UScalar.hcast .I32 digit).val≤I32.max)) at hadd
         cases headd : I32.checked_sub product (UScalar.hcast .I32 digit) with
         | none =>
           try simp only [headd] at hadd
           try simp only [headd]
           step as ⟨idx,hidx⟩
           rw [←htarget,hscan,if_neg (by simp only [I32.min_eq,I32.max_eq] at hadd; omega)]
           dsimp only [agreesNeg]
           omega
         | some sum =>
           try simp only [headd] at hadd
           simp only [headd,WP.spec_ok]
           refine ⟨?_,by omega⟩
           dsimp only [invNeg]
           have hsum : sum.val = value'.val*10-digit.val := by omega
           have hnonpos : sum.val≤0 := by omega
           refine ⟨by omega,hnonpos,by omega,?_⟩
           rw [←htarget,hscan,if_pos (by simp only [I32.min_eq,I32.max_eq] at hadd; omega)]
           simp only [scanNeg,hcursor]
           rw [show mag sum = 10*mag value'+digit.val by dsimp [mag]; omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scanNeg,boundedScan,agreesNeg,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨hi,hv,hsafe,rfl⟩

theorem checked_i32_negative_from_spec (bytes : Slice U8) (value : I32) (cursor : Usize)
 (hv : value.val≤0) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, checked_i32_negative_from bytes value cursor = .ok out ∧
   agreesNeg out (boundedScan 2147483648 true (bytes.val.map UScalar.val) (mag value) cursor.val) := by
 apply result_spec_success
 unfold checked_i32_negative_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := checked_negative_loop_spec ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hsafe)
 simpa only [scanNeg,List.drop_zero] using h

end LexicalScalarProofs