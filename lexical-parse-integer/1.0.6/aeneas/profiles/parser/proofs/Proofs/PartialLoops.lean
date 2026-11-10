import Proofs.U8
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
open LexicalParseIntegerScalarSpec

def agreesPartial (r : core.result.Result (U8 × Usize) lexical_util.error.Error) : PartialResult → Prop
 | .value v i => match r with | .Ok (x,j) => x.val=v ∧ j.val=i | _ => False
 | .overflow i => match r with | .Err (.Overflow j) => j.val=i | _ => False
 | .empty i => match r with | .Err (.Empty j) => j.val=i | _ => False

def scanPartial (it : core.slice.iter.Iter U8) (value : U8) (cursor : Usize) : PartialResult :=
 partialScan 255 ((it.slice.val.drop it.i).map UScalar.val) value.val cursor.val

def invPartial (target : PartialResult) (x : core.slice.iter.Iter U8 × U8 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scanPartial x.1 x.2.1 x.2.2=target

theorem partial_checked8_loop_spec (it : core.slice.iter.Iter U8) (value : U8) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 checked_u8_partial_from_loop it value cursor ⦃ out => agreesPartial out (scanPartial it value cursor) ⦄ := by
 unfold checked_u8_partial_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × U8 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := invPartial (scanPartial it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [invPartial] at hx
   obtain ⟨hi',hsafe',htarget⟩ := hx
   dsimp only
   unfold checked_u8_partial_from_loop.body
   by_cases hn : it'.i < it'.slice.val.length
   · have heq : core.slice.iter.IteratorSliceIter.next it' =
       .ok (some it'.slice.val[it'.i],{it' with i:=it'.i+1}) := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]; rfl
     rw [heq]
     simp only [bind_ok]
     try dsimp only
     step as ⟨cursor1,hcursor⟩
     step as ⟨d,hd⟩
     cases d with
     | none =>
       simp only [bind_ok]
       step as ⟨idx,hidx⟩
       rw [←htarget]
       simp only [scanPartial,List.drop_eq_getElem_cons hn,List.map_cons,
         partialScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agreesPartial]
       constructor
       · rfl
       · omega
     | some digit =>
       simp only [bind_ok]
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hscanPartial : scanPartial it' value' cursor' =
         if 10*value'.val+digit.val ≤ 255 then
           partialScan 255 ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*value'.val+digit.val) (cursor'.val+1)
         else .overflow cursor'.val := by
         simp only [scanPartial,List.drop_eq_getElem_cons hn,List.map_cons,
           partialScan,decimalDigit,if_pos hvalid,←hd.2.2]
       have hcast : (UScalar.cast .U8 digit).val = digit.val := by
         have h := UScalar.cast_inBounds_spec .U8 digit (by simp only [UScalar.max,UScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       simp only [show UScalar.cast .U8 10#u32 = 10#u8 by rfl,Std.lift,bind_ok]
       have hmul := U8.checked_mul_bv_spec value' 10#u8
       change (match U8.checked_mul value' 10#u8 with
         | some z => value'.val*10≤U8.max ∧ z.val=value'.val*10 ∧ z.bv=value'.bv*10#8
         | none => U8.max<value'.val*10) at hmul
       cases hemul : U8.checked_mul value' 10#u8 with
       | none =>
         try simp only [hemul] at hmul
         try simp only [hemul,bind_ok]
         step as ⟨idx,hidx⟩
         try dsimp only at hmul
         rw [←htarget,hscanPartial,if_neg (by simp only [U8.max_eq] at hmul; omega)]
         dsimp only [agreesPartial]
         omega
       | some product =>
         try simp only [hemul] at hmul
         try simp only [hemul,Std.lift,bind_ok]
         try dsimp only at hmul
         have hadd := U8.checked_add_bv_spec product (UScalar.cast .U8 digit)
         cases headd : U8.checked_add product (UScalar.cast .U8 digit) with
         | none =>
           try simp only [headd] at hadd
           simp only [headd,bind_ok]
           step as ⟨idx,hidx⟩
           rw [←htarget,hscanPartial,if_neg (by simp only [U8.max_eq] at hadd; omega)]
           dsimp only [agreesPartial]
           omega
         | some sum =>
           try simp only [headd] at hadd
           simp only [headd,bind_ok,WP.spec_ok]
           try dsimp only
           refine ⟨?_,by omega⟩
           dsimp only [invPartial]
           refine ⟨by omega,by omega,?_⟩
           rw [←htarget,hscanPartial,if_pos (by simp only [U8.max_eq] at hadd; omega)]
           simp only [scanPartial, hcursor]
           rw [show sum.val = 10*value'.val+digit.val by omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     try dsimp only
     try simp only [WP.spec_ok]
     rw [←htarget]
     simp [scanPartial,partialScan,agreesPartial,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
 · exact ⟨hi,hsafe,rfl⟩

theorem checked_u8_partial_from_spec (bytes : Slice U8) (value : U8) (cursor : Usize)
 (hsafe : cursor.val+bytes.val.length ≤ Usize.max) :
 ∃ out, checked_u8_partial_from bytes value cursor = .ok out ∧
   agreesPartial out (partialScan 255 (bytes.val.map UScalar.val) value.val cursor.val) := by
 apply result_spec_success
 unfold checked_u8_partial_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := partial_checked8_loop_spec ⟨bytes,0⟩ value cursor (by simp) (by simpa using hsafe)
 simpa only [scanPartial,List.drop_zero] using h

theorem partial_unchecked8_loop_spec (it : core.slice.iter.Iter U8) (value : U8) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length)
 (hr : it.slice.val.length-it.i≤2)
 (hbudget : value.val≤budget (it.slice.val.length-it.i))
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 unchecked_u8_partial_from_loop it value cursor ⦃ out => agreesPartial (.Ok out) (scanPartial it value cursor) ⦄ := by
 unfold unchecked_u8_partial_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × U8 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := fun x => invPartial (scanPartial it value cursor) x ∧
   x.1.slice.val.length-x.1.i≤2 ∧ x.2.1.val≤budget (x.1.slice.val.length-x.1.i))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   obtain ⟨hx,hr',hbudget'⟩ := hx
   dsimp only at hr' hbudget'
   dsimp [invPartial] at hx
   obtain ⟨hi',hsafe',htarget⟩ := hx
   dsimp only
   unfold unchecked_u8_partial_from_loop.body
   by_cases hn : it'.i < it'.slice.val.length
   · have heq : core.slice.iter.IteratorSliceIter.next it' =
       .ok (some it'.slice.val[it'.i],{it' with i:=it'.i+1}) := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]; rfl
     rw [heq]
     simp only [bind_ok]
     try dsimp only
     step as ⟨cursor1,hcursor⟩
     step as ⟨d,hd⟩
     cases d with
     | none =>
       simp only [bind_ok]
       step as ⟨idx,hidx⟩
       rw [←htarget]
       simp only [scanPartial,List.drop_eq_getElem_cons hn,List.map_cons,
         partialScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agreesPartial]
       constructor
       · rfl
       · omega
     | some digit =>
       simp only [bind_ok]
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hscanPartial : scanPartial it' value' cursor' =
         if 10*value'.val+digit.val ≤ 255 then
           partialScan 255 ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*value'.val+digit.val) (cursor'.val+1)
         else .overflow cursor'.val := by
         simp only [scanPartial,List.drop_eq_getElem_cons hn,List.map_cons,
           partialScan,decimalDigit,if_pos hvalid,←hd.2.2]
       have hcast : (UScalar.cast .U8 digit).val = digit.val := by
         have h := UScalar.cast_inBounds_spec .U8 digit (by simp only [UScalar.max,UScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hremaining : it'.slice.val.length-it'.i = 1 ∨ it'.slice.val.length-it'.i = 2 := by omega
       have hvalue : value'.val≤9 := by
         rcases hremaining with he | he <;> simp only [he,budget] at hbudget' <;> omega
       have hnext : 10*value'.val+digit.val≤99 := by omega
       simp only [show UScalar.cast .U8 10#u32 = 10#u8 by rfl,Std.lift,bind_ok,WP.spec_ok]
       let sum := core.num.U8.wrapping_add (core.num.U8.wrapping_mul value' 10#u8) (UScalar.cast .U8 digit)
       have hsum : sum.val = 10*value'.val+digit.val := by
         simp only [sum,core.num.U8.wrapping_add_val_eq,core.num.U8.wrapping_mul_val_eq,
           UScalar.ofNatCore_val_eq,hcast,UScalar.size,UScalarTy.numBits]
         norm_num only
         rw [Nat.mod_eq_of_lt (show value'.val*10<256 by omega),Nat.mod_eq_of_lt (show value'.val*10+digit.val<256 by omega)]
         omega
       change invPartial (scanPartial it value cursor) ({it' with i:=it'.i+1},sum,cursor1) ∧
           it'.slice.val.length-(it'.i+1)≤2 ∧ sum.val≤budget (it'.slice.val.length-(it'.i+1)) ∧
         it'.slice.val.length-(it'.i+1) < it'.slice.val.length-it'.i
       refine ⟨?_,by omega,?_,by omega⟩
       · dsimp only [invPartial]
         refine ⟨by omega,by omega,?_⟩
         rw [←htarget,hscanPartial,if_pos (by omega)]
         simp only [scanPartial,hcursor]
         exact congrArg (fun v => partialScan 255 ((it'.slice.val.drop (it'.i+1)).map UScalar.val) v (cursor'.val+1)) hsum
       · change sum.val≤budget (it'.slice.val.length-(it'.i+1))
         rcases hremaining with he | he
         · have he0 : it'.slice.val.length-(it'.i+1)=0 := by omega
           simp only [he0,budget]
           omega
         · have he1 : it'.slice.val.length-(it'.i+1)=1 := by omega
           simp only [he1,budget]
           simp only [he,budget] at hbudget'
           omega
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     try dsimp only
     try simp only [WP.spec_ok]
     rw [←htarget]
     simp [scanPartial,partialScan,agreesPartial,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
 · exact ⟨⟨hi,hsafe,rfl⟩,hr,hbudget⟩

theorem unchecked_u8_partial_from_spec (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤2) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, unchecked_u8_partial_from bytes 0#u8 cursor = .ok out ∧
   agreesPartial out (partialScan 255 (bytes.val.map UScalar.val) 0 cursor.val) := by
 apply result_spec_success
 unfold unchecked_u8_partial_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := partial_unchecked8_loop_spec ⟨bytes,0⟩ 0#u8 cursor (by simp) (by simpa using hlen) (by scalar_tac) (by simpa using hsafe)
 have h' : unchecked_u8_partial_from_loop ⟨bytes,0⟩ 0#u8 cursor
     ⦃ out => agreesPartial (.Ok out) (partialScan 255 (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
   simpa only [scanPartial,List.drop_zero,UScalar.ofNatCore_val_eq] using h
 apply WP.spec_bind h'
 rintro ⟨v,j⟩ hp
 change WP.spec (Result.ok (core.result.Result.Ok (v,j))) _
 exact (WP.spec_ok _).mpr hp

end LexicalScalarProofs
