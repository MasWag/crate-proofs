import UncheckedUsizeTrial
open Aeneas Aeneas.Std Result
open lexical_parse_integer_generic_front_harness lexical_parse_integer_generic_harness
open LexicalParseIntegerGenericSpec LexicalGenericComposition GenericUsizeTrial UncheckedUsizeTrial
namespace FrontUsizeTrial
private theorem usize_max64 (h : System.Platform.numBits=64) : Usize.max=18446744073709551615 := by
 simp [Usize.max,Usize.numBits,h]

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
@[step] theorem checked_wp (bytes : Slice U8) (value : Usize) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_usize bytes value cursor radix ⦃ out => agreesUsize out (scan radix.val Usize.max false false (bytes.val.map UScalar.val) value.val cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_usize_spec bytes value cursor radix hr hsafe
 rw [heq]; simpa only [WP.spec_ok] using hpost
@[step] theorem unchecked_wp (bytes : Slice U8) (value : Usize) (cursor : Usize) (radix : U32)
 (hr : 2≤radix.val ∧ radix.val≤36)
 (hb : uncheckedBound radix.val Usize.max value.val bytes.val.length)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_usize bytes value cursor radix ⦃ out => agreesUsize out (scan radix.val Usize.max false false (bytes.val.map UScalar.val) value.val cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_usize_spec radix hr bytes value cursor hb hsafe
 rw [heq]; simpa only [WP.spec_ok] using hpost
@[step] theorem overflow_digits_spec (bytes : Usize) (signed : Bool) (radix : U32)
 (hw : 1≤bytes.val ∧ bytes.val≤16) : overflow_digits bytes signed radix ⦃ out => out.val=overflowDigits bytes.val signed radix.val ⦄ := by
 unfold overflow_digits
 step*
 <;> cases signed <;> simp_all [overflowDigits,Bool.toNat] <;> omega

def agreesComplete (out : core.result.Result Usize lexical_util.error.Error) : CompleteResult → Prop
 | .value v => match out with | .Ok x => (x.val:Int)=v | _ => False
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .invalidDigit i => match out with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .overflow i => match out with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow _ => False

theorem lift_agrees {out r} (h : agreesUsize out r) : agreesComplete out (completeResult false r) := by
 cases r <;> cases out <;> simp_all [agreesUsize,agreesComplete,completeResult,signedValue,Int.ofNat_eq_natCast] <;>
 first | contradiction | (rename_i e; cases e <;> simp_all)

@[step] theorem complete_usize_tail_wp (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hplat : System.Platform.numBits=64) (hr : 2≤radix.val ∧ radix.val≤36) (hc : cursor.val≤bytes.val.length) :
 complete_usize_from_cursor bytes cursor radix ⦃ out => agreesComplete out
 (if cursor.val=bytes.val.length then .empty cursor.val else completeResult false
 (scan radix.val Usize.max false false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 have hbcount : uncheckedBound radix.val Usize.max 0 (overflowDigits 8 false radix.val) := by
   have h:=selected_prefix_safe 8 radix.val false (by simp) hr
   simpa [selectedPrefixSafe,magnitudeBound,unsignedBound,usize_max64 hplat] using h
 unfold complete_usize_from_cursor
 step*
 · simp [Slice.len_val,agreesComplete]
 · have hlen : digits.val.length≤count.val := by
     have h : digits.len≤count := by assumption
     simpa only [UScalar.le_equiv,Slice.len_val] using h
   apply unchecked_zero_shorter radix.val Usize.max digits.val.length (overflowDigits 8 false radix.val) hr.1 (by omega) hbcount
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   exact lift_agrees (by simpa only [digits_post] using out_post)
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r=.Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : scan radix.val Usize.max false false (s.val.map UScalar.val) 0 cursor.val = .value val.val (cursor.val+s.val.length) := by
     cases he : scan radix.val Usize.max false false (s.val.map UScalar.val) 0 cursor.val with
     | value n j =>
       have hj := scan_complete_consumed radix.val Usize.max false (s.val.map UScalar.val) 0 cursor.val n j he
       simp only [List.length_map] at hj
       simp only [he,agreesUsize] at r_post
       simpa only [r_post,hj]
     | invalidDigit i => simp_all [agreesUsize]
     | overflow i => simp_all [agreesUsize]
     | underflow i => simp_all [agreesUsize]
   have hd : digits.val=s.val++s1.val := by
     rw [s_post,s1_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop count.val digits.val).symm
   rw [←digits_post,hd,List.map_append,scan_append,hp]
   simp only [List.length_map,lt_self_iff_false,ite_false]
   apply lift_agrees
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
   apply lift_agrees
   cases he : scan radix.val Usize.max false false (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agreesUsize] using r_post
     exact hf.elim
   | invalidDigit i => simpa only [he] using r_post
   | overflow i => simpa only [he] using r_post
   | underflow i => simpa only [he] using r_post
@[step] theorem unsigned_start_spec (bytes : Slice U8) :
 unsigned_start bytes ⦃ cursor => cursor.val≤bytes.val.length ∧
 inputAfterSign false (bytes.val.map UScalar.val)=((bytes.val.map UScalar.val).drop cursor.val,cursor.val,false) ⦄ := by
 unfold unsigned_start
 step*
 · have hnil : bytes.val=[] := by
     apply List.eq_nil_of_length_eq_zero
     have h : b=true := by assumption
     rw [b_post] at h
     exact h
   simp [hnil,inputAfterSign]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have hb : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all [inputAfterSign]
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc : c=43#u8 := by grind
     simp [he,hc,inputAfterSign]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have hb : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all [inputAfterSign]
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc : c≠43#u8 := by grind
     have h43 : c.val≠43 := by intro h; apply hc; apply UScalar.eq_of_val_eq; simpa using h
     simp only [he,List.map_cons,inputAfterSign]
     split <;> simp_all

theorem complete_after_start (bytes : Slice U8) (cursor : Usize) (radix : U32)
 (hplat : System.Platform.numBits=64) (hc : cursor.val≤bytes.val.length)
 (hm : inputAfterSign false (bytes.val.map UScalar.val)=((bytes.val.map UScalar.val).drop cursor.val,cursor.val,false)) :
 parseComplete 64 false radix.val (bytes.val.map UScalar.val)=
 (if cursor.val=bytes.val.length then .empty cursor.val else completeResult false
 (scan radix.val Usize.max false false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) := by
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
   | cons a rest => simp [←List.map_drop,hd,he,magnitudeBound,unsignedBound,usize_max64 hplat]

theorem complete_usize_wp (bytes : Slice U8) (radix : U32)
 (hplat : System.Platform.numBits=64) (hr : 2≤radix.val ∧ radix.val≤36) :
 complete_usize bytes radix ⦃ out => agreesComplete out (parseComplete 64 false radix.val (bytes.val.map UScalar.val)) ⦄ := by
 unfold complete_usize
 step*
 rw [complete_after_start bytes i radix hplat i_post i_post1]
 exact out_post

theorem complete_usize_success (bytes : Slice U8) (radix : U32)
 (hplat : System.Platform.numBits=64) (hr : 2≤radix.val ∧ radix.val≤36) :
 ∃ out, complete_usize bytes radix=.ok out ∧ agreesComplete out (parseComplete 64 false radix.val (bytes.val.map UScalar.val)) :=
 result_spec_success (complete_usize_wp bytes radix hplat hr)
#print axioms complete_usize_success
end FrontUsizeTrial
