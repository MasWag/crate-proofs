import Proofs.I8Complete
import Proofs.I8PartialUncheckedNegative
import Proofs.I8PartialUncheckedPositive
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

@[step] theorem sign_i8_spec (bytes : Slice U8) :
 sign_i8 bytes ⦃ out => out.2.val≤bytes.val.length ∧
   signedInput (bytes.val.map UScalar.val) = ((bytes.val.map UScalar.val).drop out.2.val,out.2.val,out.1) ⦄ := by
 unfold sign_i8
 step*
 · have hnil : bytes.val=[] := by
     apply List.eq_nil_of_length_eq_zero
     have h : b=true := by assumption
     rw [b_post] at h
     exact h
   simp [hnil,signedInput]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have h : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc : c=43#u8 := by grind
     simp [he,hc,signedInput]
 · have hn : bytes.val.length≠0 := by
     intro hl
     have h : b=true := by rw [b_post]; exact hl
     contradiction
   cases he : bytes.val with
   | nil => simp_all
   | cons c rest =>
     simp only [he,List.getElem_cons_zero] at i_post
     have hc : c=45#u8 := by grind
     simp [he,hc,signedInput]
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
     simp [he,signedInput,h43,h45]


def agreesSignedComplete (out : core.result.Result I8 lexical_util.error.Error) : SignedCompleteResult → Prop
 | .value v => match out with | .Ok x => x.val=v | _ => False
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .invalidDigit i => match out with | .Err (.InvalidDigit j) => j.val=i | _ => False
 | .overflow i => match out with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow i => match out with | .Err (.Underflow j) => j.val=i | _ => False

def signedCompleteLift (negative : Bool) : CompleteResult → SignedCompleteResult
 | .empty i => .empty i
 | .scanned r => signedCompleteResult negative r

theorem lift_negative {out r} (h : agreesComplete8Negative out r) :
 agreesSignedComplete out (signedCompleteLift true r) := by
 cases r with
 | empty i => exact h
 | scanned r => cases r <;> cases out <;> simp_all [agreesComplete8Negative,agrees8Negative,signedCompleteLift,signedCompleteResult,agreesSignedComplete,signedValue,Int.ofNat_eq_natCast] <;> first | contradiction | (rename_i e; cases e <;> simp_all [agreesSignedComplete])

theorem lift_positive {out r} (h : agreesComplete8Positive out r) :
 agreesSignedComplete out (signedCompleteLift false r) := by
 cases r with
 | empty i => exact h
 | scanned r => cases r <;> cases out <;> simp_all [agreesComplete8Positive,agrees8Positive,signedCompleteLift,signedCompleteResult,agreesSignedComplete,signedValue,Int.ofNat_eq_natCast] <;> first | contradiction | (rename_i e; cases e <;> simp_all [agreesSignedComplete])

theorem complete_after_sign (bytes : Slice U8) (cursor : Usize) (negative : Bool)
 (hc : cursor.val≤bytes.val.length)
 (hm : signedInput (bytes.val.map UScalar.val) = ((bytes.val.map UScalar.val).drop cursor.val,cursor.val,negative)) :
 completeI8 (bytes.val.map UScalar.val) = signedCompleteLift negative
 (if cursor.val=bytes.val.length then .empty cursor.val else .scanned
 (boundedScan (if negative then 128 else 127) negative ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) := by
 unfold completeI8
 rw [hm]
 by_cases he : cursor.val=bytes.val.length
 · simp [he,←List.map_drop,signedCompleteLift]
 · have hn : bytes.val.drop cursor.val ≠ [] := by intro h; have hlen := congrArg List.length h; simp only [List.length_drop,List.length_nil] at hlen; omega
   cases hd : bytes.val.drop cursor.val with
   | nil => contradiction
   | cons a rest => simp [←List.map_drop,hd,he,signedCompleteLift]

@[step] theorem complete_i8_spec (bytes : Slice U8) :
 complete_i8 bytes ⦃ out => agreesSignedComplete out (completeI8 (bytes.val.map UScalar.val)) ⦄ := by
 unfold complete_i8
 step*
 · rw [complete_after_sign bytes cursor negative negative_post negative_post1]
   have hn : negative=true := by assumption
   simpa [hn] using lift_negative out_post
 · rw [complete_after_sign bytes cursor negative negative_post negative_post1]
   have hn : negative=false := by cases negative <;> simp_all
   simpa [hn] using lift_positive out_post
theorem complete_i8_success (bytes : Slice U8) :
 ∃ out, complete_i8 bytes = .ok out ∧ agreesSignedComplete out (completeI8 (bytes.val.map UScalar.val)) := by
 exact result_spec_success (complete_i8_spec bytes)

#print axioms complete_i8_success
end LexicalScalarProofs
