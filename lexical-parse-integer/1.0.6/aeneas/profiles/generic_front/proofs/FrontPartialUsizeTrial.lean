import UncheckedPartialUsizeTrial
import FrontTrial
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition GenericPartialUsizeTrial UncheckedPartialUsizeTrial FrontTrial
namespace FrontPartialUsizeTrial
private theorem usize_max64 (h : System.Platform.numBits=64) : Usize.max=18446744073709551615 := by
  simp [Usize.max,Usize.numBits,h]
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
@[step] theorem checked_wp (bytes : Slice U8) (value : Usize) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 partial.checked_usize_partial bytes value cursor radix ⦃ out => agreesUsize out (scan radix.val Usize.max false true (bytes.val.map UScalar.val) value.val cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_usize_partial_spec bytes value cursor radix hr hsafe
 rw [heq]; simpa only [WP.spec_ok] using hpost
@[step] theorem unchecked_wp (bytes : Slice U8) (value : Usize) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36)
 (hb : uncheckedBound radix.val Usize.max value.val bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_usize_partial bytes value cursor radix ⦃ out => agreesUsize out (scan radix.val Usize.max false true (bytes.val.map UScalar.val) value.val cursor.val) ∧ ∃ pair, out = .Ok pair ⦄ := by
 obtain ⟨pair,heq,hpost⟩ := unchecked_usize_partial_spec radix hr bytes value cursor hb hsafe
 rw [heq]; simpa only [WP.spec_ok] using (show agreesUsize (.Ok pair) (scan radix.val Usize.max false true (bytes.val.map UScalar.val) value.val cursor.val) ∧ ∃ q, (.Ok pair : core.result.Result (Usize × Usize) lexical_util.error.Error) = .Ok q from ⟨hpost, pair, rfl⟩)
def agreesPartial (out : core.result.Result (Usize × Usize) lexical_util.error.Error) : PartialResult → Prop
 | .value v consumed => match out with | .Ok x => (x.1.val:Int)=v ∧ x.2.val=consumed | _ => False
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .invalidDigit i => match out with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .overflow i => match out with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow _ => False

theorem lift_agrees {out r} (h : agreesUsize out r) : agreesPartial out (partialResult false r) := by
 cases r <;> cases out <;> simp_all [agreesUsize,agreesPartial,partialResult,signedValue,Int.ofNat_eq_natCast] <;>
 first | contradiction | (rename_i e; cases e <;> simp_all)

@[step] theorem partial_usize_tail_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hplat : System.Platform.numBits=64) (hr : 2≤radix.val ∧ radix.val≤36) (hc : cursor.val≤bytes.val.length) :
 partial_usize_from_cursor bytes cursor radix ⦃ out => agreesPartial out
 (if cursor.val=bytes.val.length then .empty cursor.val else partialResult false
 (scan radix.val Usize.max false true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 have hbcount : uncheckedBound radix.val Usize.max 0 (overflowDigits 8 false radix.val) := by
   have h:=selected_prefix_safe 8 radix.val false (by simp) hr
   simpa [selectedPrefixSafe,magnitudeBound,unsignedBound,usize_max64 hplat] using h
 unfold partial_usize_from_cursor
 step*
 · simp [Slice.len_val,agreesPartial]
 · have hlen : digits.val.length≤count.val := by
     have h : digits.len≤count := by assumption
     simpa only [UScalar.le_equiv,Slice.len_val] using h
   apply unchecked_zero_shorter radix.val Usize.max digits.val.length (overflowDigits 8 false radix.val) hr.1 (by omega) hbcount
 · trace_state
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   exact lift_agrees (by simpa only [digits_post] using out_post)
 · trace_state
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r=.Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   rcases val with ⟨value, ended⟩
   step*
   · have hp : scan radix.val Usize.max false true (s.val.map UScalar.val) 0 cursor.val =
       .value value.val ended.val := by
       cases he : scan radix.val Usize.max false true (s.val.map UScalar.val) 0 cursor.val with
       | value n j =>
         simp only [he, agreesUsize] at r_post
         rcases r_post with ⟨hv, hj⟩
         simpa only [he, ScanResult.value.injEq] using (show n = value.val ∧ j = ended.val by omega)
       | invalidDigit i => simp [he, agreesUsize] at r_post
       | overflow i => simp [he, agreesUsize] at r_post
       | underflow i => simp [he, agreesUsize] at r_post
     have hd : digits.val=s.val++digits.val.drop count.val := by
       rw [s_post]
       simp only [List.slice,List.drop_zero]
       exact (List.take_append_drop count.val digits.val).symm
     have hearly : ended.val < cursor.val+s.val.length := by
       have hlt : ended.val < i2.val := by
         simpa only [UScalar.lt_equiv] using (show ended < i2 by assumption)
       have hslen : s.val.length = count.val := by simpa only [Slice.len_val] using s_post1
       omega
     rw [←digits_post,hd,List.map_append,scan_append,hp]
     simp only [List.length_map,if_pos hearly]
     rw [hp] at r_post
     exact lift_agrees r_post
   · have hp : scan radix.val Usize.max false true (s.val.map UScalar.val) 0 cursor.val =
       .value value.val ended.val := by
       cases he : scan radix.val Usize.max false true (s.val.map UScalar.val) 0 cursor.val with
       | value n j =>
         simp only [he, agreesUsize] at r_post
         rcases r_post with ⟨hv, hj⟩
         simpa only [he, ScanResult.value.injEq] using (show n = value.val ∧ j = ended.val by omega)
       | invalidDigit i => simp [he, agreesUsize] at r_post
       | overflow i => simp [he, agreesUsize] at r_post
       | underflow i => simp [he, agreesUsize] at r_post
     have hslen : s.val.length = count.val := by simpa only [Slice.len_val] using s_post1
     have hj := scan_le radix.val Usize.max false true (s.val.map UScalar.val) 0 cursor.val value.val ended.val hp
     simp only [List.length_map] at hj
     have hnotearly : ¬ ended.val < cursor.val+s.val.length := by
       have hge : ¬ ended < i2 := by assumption
       have hgeval : ¬ ended.val < i2.val := by simpa only [UScalar.lt_equiv] using hge
       omega
     have hend : ended.val = i2.val := by omega
     have hd : digits.val=s.val++s1.val := by
       rw [s_post,s1_post]
       simp only [List.slice,List.drop_zero]
       exact (List.take_append_drop count.val digits.val).symm
     rw [←digits_post,hd,List.map_append,scan_append,hp]
     simp only [List.length_map,if_neg hnotearly]
     apply lift_agrees
     rw [hend]
     simpa only [s1_post] using out_post
theorem partial_after_start (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hplat : System.Platform.numBits=64)
 (hc : cursor.val≤bytes.val.length)
 (hm : inputAfterSign false (bytes.val.map UScalar.val)=((bytes.val.map UScalar.val).drop cursor.val,cursor.val,false)) :
 parsePartial 64 false radix.val (bytes.val.map UScalar.val)=
 (if cursor.val=bytes.val.length then .empty cursor.val else partialResult false
 (scan radix.val Usize.max false true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) := by
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
   | cons a rest => simp [←List.map_drop,hd,he,magnitudeBound,unsignedBound,usize_max64 hplat]

theorem partial_usize_wp (bytes : Slice U8) (radix : U32)
 (hplat : System.Platform.numBits=64)
 (hr : 2≤radix.val ∧ radix.val≤36) :
 partial_usize bytes radix ⦃ out => agreesPartial out (parsePartial 64 false radix.val (bytes.val.map UScalar.val)) ⦄ := by
 unfold partial_usize
 step*
 rw [partial_after_start bytes i radix hplat i_post i_post1]
 exact out_post

theorem partial_usize_success (bytes : Slice U8) (radix : U32)
 (hplat : System.Platform.numBits=64)
 (hr : 2≤radix.val ∧ radix.val≤36) :
 ∃ out, partial_usize bytes radix=.ok out ∧ agreesPartial out (parsePartial 64 false radix.val (bytes.val.map UScalar.val)) :=
 result_spec_success (partial_usize_wp bytes radix hplat hr)
#print axioms partial_usize_success
end FrontPartialUsizeTrial
