import SignedUncheckedI64Pos
import SignedUncheckedI64Neg
import FrontTrial
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition
namespace SignedFrontI64
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def agreesComplete (out : core.result.Result I64 lexical_util.error.Error) : CompleteResult → Prop
 | .value v => match out with | .Ok x => x.val=v | _ => False
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .invalidDigit i => match out with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .overflow i => match out with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow i => match out with | .Err (.Underflow j) => j.val=i | _ => False

section Pos
open LexicalGenericI64PosProofs SignedUncheckedI64Pos
@[step] theorem checked_positive_wp (bytes : Slice U8) (value : I64) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hv : 0≤value.val)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_i64_positive bytes value cursor radix ⦃ out => agrees8Positive out (scan radix.val 9223372036854775807 false false (bytes.val.map UScalar.val) (mag8Positive value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i64_positive_spec radix hr bytes value cursor hv hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Positive] using hpost
@[step] theorem unchecked_positive_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36)
 (hb : uncheckedBound radix.val 9223372036854775807 0 bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i64_positive bytes 0#i64 cursor radix ⦃ out => agrees8Positive out (scan radix.val 9223372036854775807 false false (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i64_positive_spec radix hr bytes 0#i64 cursor (by scalar_tac) (by simpa [mag8Positive] using hb) hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Positive] using hpost

theorem lift_positive {out r} (h : agrees8Positive out r) : agreesComplete out (completeResult false r) := by
 cases r <;> cases out <;> simp_all [agrees8Positive,agreesComplete,completeResult,signedValue,Int.ofNat_eq_natCast] <;>
 first | contradiction | (rename_i e; cases e <;> simp_all)
@[step] theorem complete_i64_positive_tail_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hc : cursor.val≤bytes.val.length) :
 complete_i64_positive_from_cursor bytes cursor radix ⦃ out => agreesComplete out
 (if cursor.val=bytes.val.length then .empty cursor.val else completeResult false
 (scan radix.val 9223372036854775807 false false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 have hbcount : uncheckedBound radix.val 9223372036854775807 0 (overflowDigits 8 true radix.val) := by
   have h:=selected_prefix_safe 8 radix.val true (by simp) hr
   dsimp [selectedPrefixSafe,magnitudeBound,positiveBound,uncheckedBound] at h
   unfold uncheckedBound
   simp only [Nat.mul_zero,Nat.zero_add]
   omega
 unfold complete_i64_positive_from_cursor
 step*
 · simp [Slice.len_val,agreesComplete]
 · have hlen : digits.val.length≤count.val := by
     have h : digits.len≤count := by assumption
     simpa only [UScalar.le_equiv,Slice.len_val] using h
   apply unchecked_zero_shorter radix.val 9223372036854775807 digits.val.length (overflowDigits 8 true radix.val) hr.1 (by omega) hbcount
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   exact lift_positive (by simpa only [digits_post] using out_post)
 · have hr : r=.Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   cases he : scan radix.val 9223372036854775807 false false (s.val.map UScalar.val) 0 cursor.val <;>
     simp_all [agrees8Positive] <;> omega
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r=.Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : scan radix.val 9223372036854775807 false false (s.val.map UScalar.val) 0 cursor.val = .value (mag8Positive val) (cursor.val+s.val.length) := by
     cases he : scan radix.val 9223372036854775807 false false (s.val.map UScalar.val) 0 cursor.val with
     | value n j =>
       have hj := scan_complete_consumed radix.val 9223372036854775807 false (s.val.map UScalar.val) 0 cursor.val n j he
       simp only [List.length_map] at hj
       simp only [he,agrees8Positive] at r_post
       have hm : n=mag8Positive val := by
         change n=val.val.toNat
         rw [r_post]
         simp
       simpa only [hm,hj]
     | invalidDigit i => simp_all [agrees8Positive]
     | overflow i => simp_all [agrees8Positive]
     | underflow i => simp_all [agrees8Positive]
   have hd : digits.val=s.val++s1.val := by
     rw [s_post,s1_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   rw [←digits_post,hd,List.map_append,scan_append,hp]
   simp only [List.length_map,lt_self_iff_false,ite_false]
   apply lift_positive
   simpa only [s_post1,i2_post] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r=.Err v := by cases r <;> simp_all
   rw [hr] at r_post
   have hd : digits.val=s.val++digits.val.drop count.val := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   rw [←digits_post,hd,List.map_append,scan_append,out_post]
   apply lift_positive
   cases he : scan radix.val 9223372036854775807 false false (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agrees8Positive] using r_post
     exact hf.elim
   | invalidDigit i => simpa only [he] using r_post
   | overflow i => simpa only [he] using r_post
   | underflow i => simpa only [he] using r_post

end Pos

section Neg
open LexicalGenericI64NegProofs SignedUncheckedI64Neg
@[step] theorem checked_negative_wp (bytes : Slice U8) (value : I64) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hv : value.val≤0)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_i64_negative bytes value cursor radix ⦃ out => agrees8Negative out (scan radix.val 9223372036854775808 true false (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i64_negative_spec radix hr bytes value cursor hv hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Negative] using hpost
@[step] theorem unchecked_negative_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36)
 (hb : uncheckedBound radix.val 9223372036854775808 0 bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i64_negative bytes 0#i64 cursor radix ⦃ out => agrees8Negative out (scan radix.val 9223372036854775808 true false (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i64_negative_spec radix hr bytes 0#i64 cursor (by scalar_tac) (by simpa [mag8Negative] using hb) hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Negative] using hpost

theorem lift_negative {out r} (h : agrees8Negative out r) : agreesComplete out (completeResult true r) := by
 cases r <;> cases out <;> simp_all [agrees8Negative,agreesComplete,completeResult,signedValue,Int.ofNat_eq_natCast] <;>
 first | contradiction | (rename_i e; cases e <;> simp_all)
@[step] theorem complete_i64_negative_tail_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hc : cursor.val≤bytes.val.length) :
 complete_i64_negative_from_cursor bytes cursor radix ⦃ out => agreesComplete out
 (if cursor.val=bytes.val.length then .empty cursor.val else completeResult true
 (scan radix.val 9223372036854775808 true false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 have hbcount : uncheckedBound radix.val 9223372036854775808 0 (overflowDigits 8 true radix.val) := by
   have h:=selected_prefix_safe 8 radix.val true (by simp) hr
   dsimp [selectedPrefixSafe,magnitudeBound,positiveBound,uncheckedBound] at h
   unfold uncheckedBound
   simp only [Nat.mul_zero,Nat.zero_add]
   omega
 unfold complete_i64_negative_from_cursor
 step*
 · simp [Slice.len_val,agreesComplete]
 · have hlen : digits.val.length≤count.val := by
     have h : digits.len≤count := by assumption
     simpa only [UScalar.le_equiv,Slice.len_val] using h
   apply unchecked_zero_shorter radix.val 9223372036854775808 digits.val.length (overflowDigits 8 true radix.val) hr.1 (by omega) hbcount
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   exact lift_negative (by simpa only [digits_post] using out_post)
 · have hr : r=.Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   cases he : scan radix.val 9223372036854775808 true false (s.val.map UScalar.val) 0 cursor.val <;>
     simp_all [agrees8Negative] <;> omega
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r=.Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : scan radix.val 9223372036854775808 true false (s.val.map UScalar.val) 0 cursor.val = .value (mag8Negative val) (cursor.val+s.val.length) := by
     cases he : scan radix.val 9223372036854775808 true false (s.val.map UScalar.val) 0 cursor.val with
     | value n j =>
       have hj := scan_complete_consumed radix.val 9223372036854775808 true (s.val.map UScalar.val) 0 cursor.val n j he
       simp only [List.length_map] at hj
       simp only [he,agrees8Negative] at r_post
       have hm : n=mag8Negative val := by
         change n=(-val.val).toNat
         rw [r_post]
         simp
       simpa only [hm,hj]
     | invalidDigit i => simp_all [agrees8Negative]
     | overflow i => simp_all [agrees8Negative]
     | underflow i => simp_all [agrees8Negative]
   have hd : digits.val=s.val++s1.val := by
     rw [s_post,s1_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   rw [←digits_post,hd,List.map_append,scan_append,hp]
   simp only [List.length_map,lt_self_iff_false,ite_false]
   apply lift_negative
   simpa only [s_post1,i2_post] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r=.Err v := by cases r <;> simp_all
   rw [hr] at r_post
   have hd : digits.val=s.val++digits.val.drop count.val := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   rw [←digits_post,hd,List.map_append,scan_append,out_post]
   apply lift_negative
   cases he : scan radix.val 9223372036854775808 true false (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agrees8Negative] using r_post
     exact hf.elim
   | invalidDigit i => simpa only [he] using r_post
   | overflow i => simpa only [he] using r_post
   | underflow i => simpa only [he] using r_post

end Neg

@[step] theorem signed_start_spec (bytes : Slice U8) :
 signed_start bytes ⦃ out => out.2.val≤bytes.val.length ∧
   inputAfterSign true (bytes.val.map UScalar.val) = ((bytes.val.map UScalar.val).drop out.2.val,out.2.val,out.1) ⦄ := by
 unfold signed_start
 step*
 · have hnil : bytes.val=[] := by
     apply List.eq_nil_of_length_eq_zero
     have h : b=true := by assumption
     rw [b_post] at h
     exact h
   simp [hnil,inputAfterSign]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have h : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc : c=43#u8 := by grind
     simp [he,hc,inputAfterSign]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have h : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc : c=45#u8 := by grind
     simp [he,hc,inputAfterSign]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have h : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc43 : c≠43#u8 := by grind
     have hc45 : c≠45#u8 := by grind
     have h43 : c.val≠43 := by intro h; apply hc43; apply UScalar.eq_of_val_eq; simpa using h
     have h45 : c.val≠45 := by intro h; apply hc45; apply UScalar.eq_of_val_eq; simpa using h
     simp [he,inputAfterSign,h43,h45]


theorem complete_after_sign (bytes : Slice U8) (cursor : Usize) (negative : Bool) (radix : U32)
 (hc : cursor.val≤bytes.val.length)
 (hm : inputAfterSign true (bytes.val.map UScalar.val)=((bytes.val.map UScalar.val).drop cursor.val,cursor.val,negative)) :
 parseComplete 64 true radix.val (bytes.val.map UScalar.val)=
 (if cursor.val=bytes.val.length then .empty cursor.val else completeResult negative
 (scan radix.val (if negative then 9223372036854775808 else 9223372036854775807) negative false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) := by
 unfold parseComplete
 rw [hm]
 by_cases he : cursor.val=bytes.val.length
 · simp [he]
 · have hn : bytes.val.drop cursor.val≠[] := by
     intro h
     have hl:=congrArg List.length h
     simp only [List.length_drop,List.length_nil] at hl
     omega
   cases hd : bytes.val.drop cursor.val with
   | nil => contradiction
   | cons a rest => simp [←List.map_drop,hd,he,magnitudeBound,positiveBound,negativeBound]

theorem complete_i64_wp (bytes : Slice U8) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) :
 complete_i64 bytes radix ⦃ out => agreesComplete out (parseComplete 64 true radix.val (bytes.val.map UScalar.val)) ⦄ := by
 unfold complete_i64
 step*
 · rw [complete_after_sign bytes cursor negative radix negative_post negative_post1]
   have hn : negative=true := by assumption
   simpa [hn] using out_post
 · rw [complete_after_sign bytes cursor negative radix negative_post negative_post1]
   have hn : negative=false := by cases negative <;> simp_all
   simpa [hn] using out_post

theorem complete_i64_success (bytes : Slice U8) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) :
 ∃ out, complete_i64 bytes radix=.ok out ∧ agreesComplete out (parseComplete 64 true radix.val (bytes.val.map UScalar.val)) :=
 result_spec_success (complete_i64_wp bytes radix hr)
#print axioms complete_i64_success
end SignedFrontI64
