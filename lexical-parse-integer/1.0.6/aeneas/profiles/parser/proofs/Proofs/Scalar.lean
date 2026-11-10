import Parser
import ScalarSpecs
open Aeneas Aeneas.Std Result
namespace LexicalScalarProofs
open lexical_parse_integer_parser_harness
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

@[step] theorem digit10_spec (c : U8) :
 lexical_util.digit.char_to_digit_const c 10#u32
 ⦃ out => match out with
    | none => ¬(48≤c.val ∧ c.val<58)
    | some d => 48≤c.val ∧ c.val<58 ∧ d.val=c.val-48 ⦄ := by
 unfold lexical_util.digit.char_to_digit_const lexical_util.digit.char_to_valid_digit_const
 simp only [le_refl,ite_true,Std.lift,bind_ok]
 split
 · rename_i hd
   simp only [WP.spec_ok]
   have hval : (UScalar.cast .U32 (core.num.U8.wrapping_sub c 48#u8)).val =
      (c.val+208)%256 := by
     simp only [U8.cast_U32_val_eq,core.num.U8.wrapping_sub_val_eq,
       UScalar.ofNatCore_val_eq,UScalar.size,UScalarTy.numBits]
     norm_num
   simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq] at hd
   have hc : c.val<256 := by scalar_tac
   omega
 · rename_i hd
   simp only [WP.spec_ok]
   have hval : (UScalar.cast .U32 (core.num.U8.wrapping_sub c 48#u8)).val =
      (c.val+208)%256 := by
     simp only [U8.cast_U32_val_eq,core.num.U8.wrapping_sub_val_eq,
       UScalar.ofNatCore_val_eq,UScalar.size,UScalarTy.numBits]
     norm_num
   simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq] at hd
   have hc : c.val<256 := by scalar_tac
   omega
open LexicalParseIntegerScalarSpec

def agrees (r : core.result.Result U32 lexical_util.error.Error) : ScanResult → Prop
 | .value v => match r with | .Ok x => x.val=v | _ => False
 | .invalidDigit i => match r with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .overflow i => match r with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow _ => False

def scan (it : core.slice.iter.Iter U8) (value : U32) (cursor : Usize) : ScanResult :=
 checkedU32Scan ((it.slice.val.drop it.i).map UScalar.val) value.val cursor.val

def inv (target : ScanResult) (x : core.slice.iter.Iter U8 × U32 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scan x.1 x.2.1 x.2.2=target

theorem checked_loop_spec (it : core.slice.iter.Iter U8) (value : U32) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 checked_u32_from_loop it value cursor ⦃ out => agrees out (scan it value cursor) ⦄ := by
 unfold checked_u32_from_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × U32 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := inv (scan it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [inv] at hx
   obtain ⟨hi',hsafe',htarget⟩ := hx
   dsimp only
   unfold checked_u32_from_loop.body
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
       simp only [scan,checkedU32Scan,List.drop_eq_getElem_cons hn,List.map_cons,
         boundedScan,decimalDigit]
       dsimp only at hd
       rw [if_neg hd]
       dsimp only [agrees]
       omega
     | some digit =>
       simp only [bind_ok]
       dsimp only at hd
       have hvalid : 48 ≤ it'.slice.val[it'.i].val ∧ it'.slice.val[it'.i].val<58 := ⟨hd.1,hd.2.1⟩
       have hscan : scan it' value' cursor' =
         if 10*value'.val+digit.val ≤ 4294967295 then
           checkedU32Scan ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (10*value'.val+digit.val) (cursor'.val+1)
         else .overflow cursor'.val := by
         simp only [scan,checkedU32Scan,List.drop_eq_getElem_cons hn,List.map_cons,
           boundedScan,decimalDigit,if_pos hvalid,←hd.2.2]
         simp only [Bool.false_eq_true,reduceIte]
       step as ⟨mul,hmul⟩
       cases mul with
       | none =>
         simp only [bind_ok]
         step as ⟨idx,hidx⟩
         dsimp only at hmul
         rw [←htarget,hscan,if_neg (by simp only [U32.max_eq] at hmul; omega)]
         dsimp only [agrees]
         omega
       | some product =>
         simp only [bind_ok]
         dsimp only at hmul
         have hadd := U32.checked_add_bv_spec product digit
         cases headd : U32.checked_add product digit with
         | none =>
           simp only [headd] at hadd
           simp only [headd,bind_ok]
           step as ⟨idx,hidx⟩
           rw [←htarget,hscan,if_neg (by simp only [U32.max_eq] at hadd; omega)]
           dsimp only [agrees]
           omega
         | some sum =>
           simp only [headd] at hadd
           simp only [headd,bind_ok,WP.spec_ok]
           try dsimp only
           refine ⟨?_,by omega⟩
           dsimp only [inv]
           refine ⟨by omega,by omega,?_⟩
           rw [←htarget,hscan,if_pos (by simp only [U32.max_eq] at hadd; omega)]
           simp only [scan, hcursor]
           rw [show sum.val = 10*value'.val+digit.val by omega]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     try dsimp only
     try simp only [WP.spec_ok]
     rw [←htarget]
     simp [scan,checkedU32Scan,boundedScan,agrees,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
 · exact ⟨hi,hsafe,rfl⟩

unseal Result in
theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
 (h : m ⦃ out => p out ⦄) : ∃ out, m = .ok out ∧ p out := by
 unfold Aeneas.Std.WP.spec at h
 exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
   (fun value _ hp => ⟨value,rfl,hp⟩)
   (fun effect _ _ hfalse => False.elim hfalse)

theorem checked_u32_from_spec (bytes : Slice U8) (value : U32) (cursor : Usize)
 (hsafe : cursor.val+bytes.val.length ≤ Usize.max) :
 ∃ out, checked_u32_from bytes value cursor = .ok out ∧
   agrees out (checkedU32Scan (bytes.val.map UScalar.val) value.val cursor.val) := by
 apply result_spec_success
 unfold checked_u32_from
 simp only [core.slice.Slice.iter,bind_ok]
 have h := checked_loop_spec ⟨bytes,0⟩ value cursor (by simp) (by simpa using hsafe)
 simpa only [scan,List.drop_zero] using h

theorem checked_u32_spec (bytes : Slice U8) (value : U32) :
 ∃ out, checked_u32 bytes value = .ok out ∧
   agrees out (checkedU32Scan (bytes.val.map UScalar.val) value.val 0) := by
 unfold checked_u32
 exact checked_u32_from_spec bytes value 0#usize (by scalar_tac)

end LexicalScalarProofs