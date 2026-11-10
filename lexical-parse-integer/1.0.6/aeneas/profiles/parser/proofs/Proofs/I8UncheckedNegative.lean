import Proofs.I8Positive
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
theorem unchecked_negative8_loop_spec (it : core.slice.iter.Iter U8) (value : I8) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length)
 (hr : it.slice.val.length-it.i≤1)
 (hz : it.slice.val.length-it.i=1 → value.val=0) (hv : value.val≤0)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 unchecked_i8_negative_from_loop it value cursor ⦃ out => agrees8Negative out (scan8Negative it value cursor) ⦄ := by
 unfold unchecked_i8_negative_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I8 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := fun x => inv8Negative (scan8Negative it value cursor) x ∧
     x.1.slice.val.length-x.1.i≤1 ∧ (x.1.slice.val.length-x.1.i=1 → x.2.1.val=0))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   obtain ⟨hx,hr',hz'⟩ := hx
   dsimp only at hr' hz'
   dsimp [inv8Negative] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmag : (mag8Negative value' : Int) = -value'.val := by simp [mag8Negative,Int.toNat_of_nonneg (by omega : 0≤ -value'.val)]
   dsimp only
   unfold unchecked_i8_negative_from_loop.body
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
       have hzero : value'.val=0 := hz' (by omega)
       have hvalue : value'=0#i8 := IScalar.eq_of_val_eq (by simpa using hzero)
       simp only [show UScalar.hcast .I8 10#u32 = 10#i8 by rfl,Std.lift,bind_ok,hvalue,
         show core.num.I8.wrapping_mul 0#i8 10#i8 = 0#i8 by rfl,WP.spec_ok]
       let sum := core.num.I8.wrapping_sub 0#i8 (UScalar.hcast .I8 digit)
       have hsum : sum.val = -(digit.val : Int) := by
         simp only [sum,core.num.I8.wrapping_sub_val_eq,show (0#i8:I8).val=0 by rfl,hcast]
         norm_num only [Int.zero_sub,Int.zero_add]
         apply Int.bmod_eq_of_le <;> omega
       change inv8Negative (scan8Negative it value cursor) ({it' with i:=it'.i+1},sum,cursor1) ∧
         it'.slice.val.length-(it'.i+1)≤1 ∧
         (it'.slice.val.length-(it'.i+1)=1 → sum.val=0) ∧
         it'.slice.val.length-(it'.i+1) < it'.slice.val.length-it'.i
       refine ⟨?_,by omega,by omega,by omega⟩
       dsimp only [inv8Negative]
       refine ⟨by omega,by omega,by omega,?_⟩
       rw [←htarget,hscan,if_pos (by dsimp [mag8Negative]; omega)]
       simp only [scan8Negative,hcursor]
       rw [show mag8Negative sum = 10*mag8Negative value'+digit.val by dsimp [mag8Negative]; omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scan8Negative,boundedScan,agrees8Negative,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨⟨hi,hv,hsafe,rfl⟩,hr,hz⟩

theorem unchecked_i8_negative_from_spec (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤1) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, unchecked_i8_negative_from bytes 0#i8 cursor = .ok out ∧
   agrees8Negative out (boundedScan 128 true (bytes.val.map UScalar.val) 0 cursor.val) := by
 apply result_spec_success
 unfold unchecked_i8_negative_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := unchecked_negative8_loop_spec ⟨bytes,0⟩ 0#i8 cursor (by simp) (by simpa using hlen) (by simp) (by scalar_tac) (by simpa using hsafe)
 simpa [scan8Negative,mag8Negative] using h

end LexicalScalarProofs
