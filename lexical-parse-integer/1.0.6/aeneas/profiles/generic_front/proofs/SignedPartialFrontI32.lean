import SignedPartialUncheckedI32Pos
import SignedPartialUncheckedI32Neg
import SignedFrontI32
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition
namespace SignedPartialFrontI32
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def agreesPartial (out : core.result.Result (I32 × Usize) lexical_util.error.Error) : PartialResult → Prop
 | .value v i => match out with | .Ok (x,j) => x.val=v ∧ j.val=i | _ => False
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .invalidDigit _ => False
 | .overflow i => match out with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow i => match out with | .Err (.Underflow j) => j.val=i | _ => False

section Pos
open GenericPartialI32PosTrial SignedPartialUncheckedI32Pos
@[step] theorem checked_positive_wp (bytes : Slice U8) (value : I32) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hv : 0≤value.val)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 partial.checked_i32_positive_partial bytes value cursor radix ⦃ out => agrees8Positive out (scan radix.val 2147483647 false true (bytes.val.map UScalar.val) (mag8Positive value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i32_positive_partial_spec radix hr bytes value cursor hv hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Positive] using hpost
@[step] theorem unchecked_positive_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36)
 (hb : uncheckedBound radix.val 2147483647 0 bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i32_positive_partial bytes 0#i32 cursor radix ⦃ out => agrees8Positive out (scan radix.val 2147483647 false true (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i32_positive_partial_spec radix hr bytes 0#i32 cursor (by scalar_tac) (by simpa [mag8Positive] using hb) hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Positive] using hpost

theorem lift_positive {out r} (h : agrees8Positive out r) : agreesPartial out (partialResult false r) := by
 cases r <;> cases out <;> simp_all [agrees8Positive,agreesPartial,partialResult,signedValue,Int.ofNat_eq_natCast] <;>
 first | contradiction | (rename_i e; cases e <;> simp_all)

@[step] theorem partial_i32_positive_tail_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hc : cursor.val≤bytes.val.length) :
 partial_i32_positive_from_cursor bytes cursor radix ⦃ out => agreesPartial out
 (if cursor.val=bytes.val.length then .empty cursor.val else partialResult false
 (scan radix.val 2147483647 false true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 have hbcount : uncheckedBound radix.val 2147483647 0 (overflowDigits 4 true radix.val) := by
   have h:=selected_prefix_safe 4 radix.val true (by simp) hr
   dsimp [selectedPrefixSafe,magnitudeBound,positiveBound,uncheckedBound] at h
   unfold uncheckedBound
   simp only [Nat.mul_zero,Nat.zero_add]
   omega
 unfold partial_i32_positive_from_cursor
 step*
 · simp [agreesPartial]
 · have hlen : digits.val.length≤count.val := by
     have h : digits.len≤count := by assumption
     simpa only [UScalar.le_equiv,Slice.len_val] using h
   apply unchecked_zero_shorter radix.val 2147483647 digits.val.length (overflowDigits 4 true radix.val) hr.1 (by omega) hbcount
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   exact lift_positive (by simpa only [digits_post] using out_post)
 · rcases val with ⟨value,ended⟩
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   have hr : r=.Ok (value,ended) := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : scan radix.val 2147483647 false true (s.val.map UScalar.val) 0 cursor.val = .value (mag8Positive value) ended.val := by
     cases he : scan radix.val 2147483647 false true (s.val.map UScalar.val) 0 cursor.val with
     | value n j =>
       simp only [he,agrees8Positive] at r_post
       have hm : n=mag8Positive value := by
         change n=value.val.toNat
         rw [r_post.1]
         simp
       simpa only [hm,r_post.2]
     | invalidDigit i => simp_all [agrees8Positive]
     | overflow i => simp_all [agrees8Positive]
     | underflow i => simp_all [agrees8Positive]
   have hslen : s.val.length=count.val := s_post1
   have hle := scan_le radix.val 2147483647 false true (s.val.map UScalar.val) 0 cursor.val (mag8Positive value) ended.val hp
   simp only [List.length_map,hslen] at hle
   have hd : digits.val=s.val++digits.val.drop count.val := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   simp only [if_neg hne]
   step*
   · rw [←digits_post,hd,List.map_append,scan_append,hp]
     simp only [List.length_map,hslen]
     have hlt : ended.val < i2.val := by
       have h : ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     rw [if_pos (by omega)]
     apply lift_positive
     simpa only [hp] using r_post
   · cases he : scan radix.val 2147483647 false true (s.val.map UScalar.val) 0 cursor.val <;>
       simp only [he,agrees8Positive] at r_post <;> omega
   · rw [←digits_post,hd,List.map_append,scan_append,hp]
     simp only [List.length_map,hslen]
     have hnlt : ¬ended.val < i2.val := by
       have h : ¬ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     have hend : ended.val=cursor.val+count.val := by omega
     rw [if_neg (by omega)]
     apply lift_positive
     simpa only [s1_post,i2_post,hend] using out_post
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
   cases he : scan radix.val 2147483647 false true (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agrees8Positive] using r_post
     exact hf.elim
   | invalidDigit i => simpa only [he] using r_post
   | overflow i => simpa only [he] using r_post
   | underflow i => simpa only [he] using r_post
end Pos

section Neg
open GenericPartialI32NegTrial SignedPartialUncheckedI32Neg
@[step] theorem checked_negative_wp (bytes : Slice U8) (value : I32) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hv : value.val≤0)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 partial.checked_i32_negative_partial bytes value cursor radix ⦃ out => agrees8Negative out (scan radix.val 2147483648 true true (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i32_negative_partial_spec radix hr bytes value cursor hv hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Negative] using hpost
@[step] theorem unchecked_negative_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36)
 (hb : uncheckedBound radix.val 2147483648 0 bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i32_negative_partial bytes 0#i32 cursor radix ⦃ out => agrees8Negative out (scan radix.val 2147483648 true true (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i32_negative_partial_spec radix hr bytes 0#i32 cursor (by scalar_tac) (by simpa [mag8Negative] using hb) hsafe
 rw [heq]; simpa [WP.spec_ok,mag8Negative] using hpost

theorem lift_negative {out r} (h : agrees8Negative out r) : agreesPartial out (partialResult true r) := by
 cases r <;> cases out <;> simp_all [agrees8Negative,agreesPartial,partialResult,signedValue,Int.ofNat_eq_natCast] <;>
 first | contradiction | (rename_i e; cases e <;> simp_all)

@[step] theorem partial_i32_negative_tail_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hc : cursor.val≤bytes.val.length) :
 partial_i32_negative_from_cursor bytes cursor radix ⦃ out => agreesPartial out
 (if cursor.val=bytes.val.length then .empty cursor.val else partialResult true
 (scan radix.val 2147483648 true true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 have hbcount : uncheckedBound radix.val 2147483648 0 (overflowDigits 4 true radix.val) := by
   have h:=selected_prefix_safe 4 radix.val true (by simp) hr
   dsimp [selectedPrefixSafe,magnitudeBound,positiveBound,uncheckedBound] at h
   unfold uncheckedBound
   simp only [Nat.mul_zero,Nat.zero_add]
   omega
 unfold partial_i32_negative_from_cursor
 step*
 · simp [agreesPartial]
 · have hlen : digits.val.length≤count.val := by
     have h : digits.len≤count := by assumption
     simpa only [UScalar.le_equiv,Slice.len_val] using h
   apply unchecked_zero_shorter radix.val 2147483648 digits.val.length (overflowDigits 4 true radix.val) hr.1 (by omega) hbcount
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   exact lift_negative (by simpa only [digits_post] using out_post)
 · rcases val with ⟨value,ended⟩
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   have hr : r=.Ok (value,ended) := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : scan radix.val 2147483648 true true (s.val.map UScalar.val) 0 cursor.val = .value (mag8Negative value) ended.val := by
     cases he : scan radix.val 2147483648 true true (s.val.map UScalar.val) 0 cursor.val with
     | value n j =>
       simp only [he,agrees8Negative] at r_post
       have hm : n=mag8Negative value := by
         change n=(-value.val).toNat
         rw [r_post.1]
         simp
       simpa only [hm,r_post.2]
     | invalidDigit i => simp_all [agrees8Negative]
     | overflow i => simp_all [agrees8Negative]
     | underflow i => simp_all [agrees8Negative]
   have hslen : s.val.length=count.val := s_post1
   have hle := scan_le radix.val 2147483648 true true (s.val.map UScalar.val) 0 cursor.val (mag8Negative value) ended.val hp
   simp only [List.length_map,hslen] at hle
   have hd : digits.val=s.val++digits.val.drop count.val := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   simp only [if_neg hne]
   step*
   · rw [←digits_post,hd,List.map_append,scan_append,hp]
     simp only [List.length_map,hslen]
     have hlt : ended.val < i2.val := by
       have h : ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     rw [if_pos (by omega)]
     apply lift_negative
     simpa only [hp] using r_post
   · cases he : scan radix.val 2147483648 true true (s.val.map UScalar.val) 0 cursor.val <;>
       simp only [he,agrees8Negative] at r_post <;> omega
   · rw [←digits_post,hd,List.map_append,scan_append,hp]
     simp only [List.length_map,hslen]
     have hnlt : ¬ended.val < i2.val := by
       have h : ¬ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     have hend : ended.val=cursor.val+count.val := by omega
     rw [if_neg (by omega)]
     apply lift_negative
     simpa only [s1_post,i2_post,hend] using out_post
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
   cases he : scan radix.val 2147483648 true true (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agrees8Negative] using r_post
     exact hf.elim
   | invalidDigit i => simpa only [he] using r_post
   | overflow i => simpa only [he] using r_post
   | underflow i => simpa only [he] using r_post
end Neg

theorem partial_after_sign (bytes : Slice U8) (cursor : Usize) (negative : Bool) (radix : U32)
 (hc : cursor.val≤bytes.val.length)
 (hm : inputAfterSign true (bytes.val.map UScalar.val)=((bytes.val.map UScalar.val).drop cursor.val,cursor.val,negative)) :
 parsePartial 32 true radix.val (bytes.val.map UScalar.val)=
 (if cursor.val=bytes.val.length then .empty cursor.val else partialResult negative
 (scan radix.val (if negative then 2147483648 else 2147483647) negative true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) := by
 unfold parsePartial
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

theorem partial_i32_wp (bytes : Slice U8) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) :
 partial_i32 bytes radix ⦃ out => agreesPartial out (parsePartial 32 true radix.val (bytes.val.map UScalar.val)) ⦄ := by
 unfold partial_i32
 step*
 · rw [partial_after_sign bytes cursor negative radix negative_post negative_post1]
   have hn : negative=true := by assumption
   simpa [hn] using out_post
 · rw [partial_after_sign bytes cursor negative radix negative_post negative_post1]
   have hn : negative=false := by cases negative <;> simp_all
   simpa [hn] using out_post

theorem partial_i32_success (bytes : Slice U8) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) :
 ∃ out, partial_i32 bytes radix=.ok out ∧ agreesPartial out (parsePartial 32 true radix.val (bytes.val.map UScalar.val)) :=
 result_spec_success (partial_i32_wp bytes radix hr)
#print axioms partial_i32_success
end SignedPartialFrontI32
