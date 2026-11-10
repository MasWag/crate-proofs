import Proofs.Signed
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def magPos (value : I32) : Nat := value.val.toNat

def scanPos (it : core.slice.iter.Iter U8) (value : I32) (cursor : Usize) :=
 boundedScan 2147483647 false ((it.slice.val.drop it.i).map UScalar.val) (magPos value) cursor.val

def agreesPos (r : core.result.Result I32 lexical_util.error.Error) : ScanResult → Prop
 | .value v => match r with | .Ok x => x.val = (v : Int) | _ => False
 | .invalidDigit i => match r with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .overflow i => match r with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow _ => False

def invPos (target : ScanResult) (x : core.slice.iter.Iter U8 × I32 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧ 0≤x.2.1.val ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scanPos x.1 x.2.1 x.2.2=target

theorem checked_positive_loop_spec (it : core.slice.iter.Iter U8) (value : I32) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : 0≤value.val)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 checked_i32_positive_from_loop it value cursor ⦃ out => agreesPos out (scanPos it value cursor) ⦄ := by
 unfold checked_i32_positive_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I32 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := invPos (scanPos it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [invPos] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmagPos : (magPos value' : Int) = value'.val := by simp [magPos,Int.toNat_of_nonneg (by omega : 0≤ value'.val)]
   dsimp only
   unfold checked_i32_positive_from_loop.body
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
       simp only [scanPos,List.drop_eq_getElem_cons hn,List.map_cons,boundedScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agreesPos]
       omega
     | some digit =>
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hcast : (UScalar.hcast .I32 digit).val = digit.val := by
         have h := UScalar.hcast_inBounds_spec .I32 digit (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hscan : scanPos it' value' cursor' =
         if 10*magPos value'+digit.val ≤ 2147483647 then
           boundedScan 2147483647 false ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*magPos value'+digit.val) (cursor'.val+1)
         else .overflow cursor'.val := by
         simp only [scanPos,List.drop_eq_getElem_cons hn,List.map_cons,
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
         dsimp only [agreesPos]
         omega
       | some product =>
         try simp only [hemul] at hmul
         try simp only [hemul,Std.lift,bind_ok]
         try dsimp only at hmul
         have hadd := I32.checked_add_bv_spec product (UScalar.hcast .I32 digit)
         change (match I32.checked_add product (UScalar.hcast .I32 digit) with
           | some z => I32.min≤product.val+(UScalar.hcast .I32 digit).val ∧
               product.val+(UScalar.hcast .I32 digit).val≤I32.max ∧
               z.val=product.val+(UScalar.hcast .I32 digit).val ∧
               z.bv=product.bv+I32.bv (UScalar.hcast .I32 digit)
           | none => ¬(I32.min≤product.val+(UScalar.hcast .I32 digit).val ∧
               product.val+(UScalar.hcast .I32 digit).val≤I32.max)) at hadd
         cases headd : I32.checked_add product (UScalar.hcast .I32 digit) with
         | none =>
           try simp only [headd] at hadd
           try simp only [headd]
           step as ⟨idx,hidx⟩
           rw [←htarget,hscan,if_neg (by simp only [I32.min_eq,I32.max_eq] at hadd; omega)]
           dsimp only [agreesPos]
           omega
         | some sum =>
           try simp only [headd] at hadd
           simp only [headd,WP.spec_ok]
           refine ⟨?_,by omega⟩
           dsimp only [invPos]
           have hsum : sum.val = value'.val*10+digit.val := by omega
           have hnonpos : 0≤sum.val := by omega
           refine ⟨by omega,hnonpos,by omega,?_⟩
           rw [←htarget,hscan,if_pos (by simp only [I32.min_eq,I32.max_eq] at hadd; omega)]
           simp only [scanPos,hcursor]
           rw [show magPos sum = 10*magPos value'+digit.val by dsimp [magPos]; omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scanPos,boundedScan,agreesPos,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨hi,hv,hsafe,rfl⟩

theorem checked_i32_positive_from_spec (bytes : Slice U8) (value : I32) (cursor : Usize)
 (hv : 0≤value.val) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, checked_i32_positive_from bytes value cursor = .ok out ∧
   agreesPos out (boundedScan 2147483647 false (bytes.val.map UScalar.val) (magPos value) cursor.val) := by
 apply result_spec_success
 unfold checked_i32_positive_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := checked_positive_loop_spec ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hsafe)
 simpa only [scanPos,List.drop_zero] using h

end LexicalScalarProofs