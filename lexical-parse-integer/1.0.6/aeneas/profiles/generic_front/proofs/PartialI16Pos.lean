import GenericDigit
import GenericScalarSpecs
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness LexicalParseIntegerGenericSpec
namespace GenericPartialI16PosTrial
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def mag8Positive (value : I16) : Nat := value.val.toNat

def scan8Positive (radix : U32) (it : core.slice.iter.Iter U8) (value : I16) (cursor : Usize) :=
 scan radix.val 32767 false true ((it.slice.val.drop it.i).map UScalar.val) (mag8Positive value) cursor.val

def agrees8Positive (r : core.result.Result (I16 × Usize) lexical_util.error.Error) : ScanResult → Prop
 | .value v consumed => match r with | .Ok x => x.1.val = (v : Int) ∧ x.2.val = consumed | _ => False
 | .invalidDigit _ => False
 | .overflow i => match r with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow _ => False

def inv8Positive (radix : U32) (target : ScanResult) (x : core.slice.iter.Iter U8 × I16 × Usize) : Prop :=
 x.1.i ≤ x.1.slice.val.length ∧ 0≤x.2.1.val ∧
 x.2.2.val+(x.1.slice.val.length-x.1.i) ≤ Usize.max ∧
 scan8Positive radix x.1 x.2.1 x.2.2=target

theorem checked_positive8_loop_spec (radix : U32) (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) (it : core.slice.iter.Iter U8) (value : I16) (cursor : Usize)
 (hi : it.i ≤ it.slice.val.length) (hv : 0≤value.val)
 (hsafe : cursor.val+(it.slice.val.length-it.i)≤Usize.max) :
 partial.checked_i16_positive_partial_loop it value cursor radix ⦃ out => agrees8Positive out (scan8Positive radix it value cursor) ⦄ := by
 unfold partial.checked_i16_positive_partial_loop
 apply loop.spec_decr_nat
   (measure := fun (x : core.slice.iter.Iter U8 × I16 × Usize) => x.1.slice.val.length-x.1.i)
   (inv := inv8Positive radix (scan8Positive radix it value cursor))
 · intro x hx
   rcases x with ⟨it',value',cursor'⟩
   dsimp [inv8Positive] at hx
   obtain ⟨hi',hv',hsafe',htarget⟩ := hx
   have hmagPos : (mag8Positive value' : Int) = value'.val := by simp [mag8Positive,Int.toNat_of_nonneg (by omega : 0≤ value'.val)]
   dsimp only
   unfold partial.checked_i16_positive_partial_loop.body
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
       simp
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
       have hscan : scan8Positive radix it' value' cursor' =
         if radix.val*mag8Positive value'+digit.val ≤ 32767 then
           scan radix.val 32767 false true ((it'.slice.val.drop (it'.i+1)).map UScalar.val)
             (radix.val*mag8Positive value'+digit.val) (cursor'.val+1)
         else .overflow cursor'.val := by
         simp only [scan8Positive,List.drop_eq_getElem_cons hn,List.map_cons,
           scan,←hd]
         simp
       step as ⟨radix8, hradix8⟩
       have hradixval : radix8.val = radix.val := by
         rw [hradix8]
         have h := UScalar.hcast_inBounds_spec .I16 radix (by simp only [IScalar.max,IScalarTy.numBits]; omega)
         simpa only [Std.lift,WP.spec_ok] using h
       have hterm : (↑(radix.val * mag8Positive value') : Int) = value'.val * radix8.val := by
         simp [Nat.cast_mul, hmagPos, hradixval, mul_comm]
       have hprodNonneg : 0 ≤ value'.val * radix8.val := mul_nonneg hv' (by omega)
       have hmul := I16.checked_mul_bv_spec value' radix8
       change (match I16.checked_mul value' radix8 with
         | some z => I16.min≤value'.val*radix8.val ∧ value'.val*radix8.val≤I16.max ∧
             z.val=value'.val*radix8.val ∧ z.bv=value'.bv*radix8.bv
         | none => ¬(I16.min≤value'.val*radix8.val ∧ value'.val*radix8.val≤I16.max)) at hmul
       cases hemul : I16.checked_mul value' radix8 with
       | none =>
         try simp only [hemul] at hmul
         simp only [Std.lift, bind_ok]
         step as ⟨idx,hidx⟩
         try dsimp only at hmul
         rw [←htarget,hscan,if_neg (by simp only [I16.min_eq,I16.max_eq] at hmul; omega)]
         dsimp only [agrees8Positive]
         omega
       | some product =>
         try simp only [hemul] at hmul
         try simp only [hemul,Std.lift,bind_ok]
         try dsimp only at hmul
         have hadd := I16.checked_add_bv_spec product (UScalar.hcast .I16 digit)
         change (match I16.checked_add product (UScalar.hcast .I16 digit) with
           | some z => I16.min≤product.val+(UScalar.hcast .I16 digit).val ∧
               product.val+(UScalar.hcast .I16 digit).val≤I16.max ∧
               z.val=product.val+(UScalar.hcast .I16 digit).val ∧
               z.bv=product.bv+I16.bv (UScalar.hcast .I16 digit)
           | none => ¬(I16.min≤product.val+(UScalar.hcast .I16 digit).val ∧
               product.val+(UScalar.hcast .I16 digit).val≤I16.max)) at hadd
         cases headd : I16.checked_add product (UScalar.hcast .I16 digit) with
         | none =>
           try simp only [headd] at hadd
           try simp only [headd]
           step as ⟨idx,hidx⟩
           rw [←htarget,hscan,if_neg (by simp only [I16.min_eq,I16.max_eq] at hadd; omega)]
           dsimp only [agrees8Positive]
           omega
         | some sum =>
           try simp only [headd] at hadd
           simp only [headd,WP.spec_ok]
           refine ⟨?_,by omega⟩
           dsimp only [inv8Positive]
           have hsum : sum.val = value'.val*radix.val+digit.val := by rw [←hradixval]; omega
           have hnonpos : 0≤sum.val := by omega
           refine ⟨by omega,hnonpos,by omega,?_⟩
           rw [←htarget,hscan,if_pos (by simp only [I16.min_eq,I16.max_eq] at hadd; omega)]
           simp only [scan8Positive,hcursor]
           have hsumNat : (↑(radix.val * mag8Positive value' + digit.val) : Int) = sum.val := by
             simp only [Nat.cast_add]
             rw [hterm]
             rw [←hradixval] at hsum
             omega
           rw [show mag8Positive sum = radix.val*mag8Positive value'+digit.val by
             dsimp [mag8Positive]
             rw [← Int.toNat_natCast (radix.val * value'.val.toNat + digit.val)]
             exact congrArg Int.toNat hsumNat.symm]
   · have heq : core.slice.iter.IteratorSliceIter.next it' = .ok (none,it') := by
       simp [core.slice.iter.IteratorSliceIter.next,hn]
     rw [heq]
     simp only [bind_ok]
     rw [←htarget]
     simp [scan8Positive,scan,agrees8Positive,List.drop_eq_nil_iff.mpr (by omega : it'.slice.val.length ≤ it'.i)]
     omega
 · exact ⟨hi,hv,hsafe,rfl⟩

unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun v _ hp => ⟨v, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem checked_i16_positive_partial_spec (radix : U32) (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) (bytes : Slice U8) (value : I16) (cursor : Usize)
 (hv : 0≤value.val) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 ∃ out, partial.checked_i16_positive_partial bytes value cursor radix = .ok out ∧
   agrees8Positive out (scan radix.val 32767 false true (bytes.val.map UScalar.val) (mag8Positive value) cursor.val) := by
 apply result_spec_success
 unfold partial.checked_i16_positive_partial
 simp only [core.slice.Slice.iter,bind_ok]
 have h := checked_positive8_loop_spec radix hr ⟨bytes,0⟩ value cursor (by simp) hv (by simpa using hsafe)
 simpa only [scan8Positive,List.drop_zero] using h

end GenericPartialI16PosTrial