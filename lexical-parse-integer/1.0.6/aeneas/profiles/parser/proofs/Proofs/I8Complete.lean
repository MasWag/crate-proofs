import Proofs.Complete
import Proofs.I8UncheckedPositive
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def agreesComplete8Negative (out : core.result.Result I8 lexical_util.error.Error) : CompleteResult → Prop
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .scanned result => agrees8Negative out result

@[step] theorem checked8Negative_wp (bytes : Slice U8) (value : I8) (cursor : Usize)
 (hv : value.val≤0) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_i8_negative_from bytes value cursor ⦃ out => agrees8Negative out (boundedScan 128 true (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i8_negative_from_spec bytes value cursor hv hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem unchecked8Negative_wp (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤1) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i8_negative_from bytes 0#i8 cursor ⦃ out => agrees8Negative out (boundedScan 128 true (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i8_negative_from_spec bytes cursor hlen hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem complete_i8_negative_tail_spec (bytes : Slice U8) (cursor : Usize)
 (hc : cursor.val≤bytes.val.length) :
 complete_i8_negative_from_cursor bytes cursor ⦃ out => agreesComplete8Negative out
   (if cursor.val=bytes.val.length then .empty cursor.val else
    .scanned (boundedScan 128 true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 unfold complete_i8_negative_from_cursor
 step*
 · simp [Slice.len_val,agreesComplete8Negative]
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8Negative]
   simpa only [digits_post] using out_post
 · have hr : r = .Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   cases he : boundedScan 128 true (s.val.map UScalar.val) 0 cursor.val <;>
     simp_all [agrees8Negative] <;> omega
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8Negative]
   have hr : r = .Ok val := by
     cases r with
     | Ok v => simp_all
     | Err e => simp_all
   rw [hr] at r_post
   have hp : boundedScan 128 true (s.val.map UScalar.val) 0 cursor.val = .value (mag8Negative val) := by
     cases he : boundedScan 128 true (s.val.map UScalar.val) 0 cursor.val <;> simp_all [agrees8Negative,mag8Negative]
   have hd : digits.val = s.val++s1.val := by
     rw [s_post,s1_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   rw [←digits_post,hd,List.map_append,boundedScan_append,hp]
   have hslen : s.val.length=1 := s_post1
   simpa only [s1_post,i2_post,List.length_map,hslen] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8Negative]
   have hr : r = .Err v := by
     cases r with
     | Ok a => simp_all
     | Err a => simp_all
   rw [hr] at r_post
   have hd : digits.val = s.val++(digits.val.drop 1) := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   rw [←digits_post,hd,List.map_append,boundedScan_append,out_post]
   cases he : boundedScan 128 true (s.val.map UScalar.val) 0 cursor.val with
   | value n =>
     have hf : False := by simpa only [he,agrees8Negative] using r_post
     exact hf.elim
   | invalidDigit n => simpa only [he] using r_post
   | overflow n => simpa only [he] using r_post
   | underflow n => simpa only [he] using r_post


def agreesComplete8Positive (out : core.result.Result I8 lexical_util.error.Error) : CompleteResult → Prop
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .scanned result => agrees8Positive out result

@[step] theorem checked8Positive_wp (bytes : Slice U8) (value : I8) (cursor : Usize)
 (hv : 0≤value.val) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_i8_positive_from bytes value cursor ⦃ out => agrees8Positive out (boundedScan 127 false (bytes.val.map UScalar.val) (mag8Positive value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i8_positive_from_spec bytes value cursor hv hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem unchecked8Positive_wp (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤1) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i8_positive_from bytes 0#i8 cursor ⦃ out => agrees8Positive out (boundedScan 127 false (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i8_positive_from_spec bytes cursor hlen hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem complete_i8_positive_tail_spec (bytes : Slice U8) (cursor : Usize)
 (hc : cursor.val≤bytes.val.length) :
 complete_i8_positive_from_cursor bytes cursor ⦃ out => agreesComplete8Positive out
   (if cursor.val=bytes.val.length then .empty cursor.val else
    .scanned (boundedScan 127 false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 unfold complete_i8_positive_from_cursor
 step*
 · simp [Slice.len_val,agreesComplete8Positive]
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8Positive]
   simpa only [digits_post] using out_post
 · have hr : r = .Ok val := by cases r <;> simp_all
   rw [hr] at r_post
   cases he : boundedScan 127 false (s.val.map UScalar.val) 0 cursor.val <;>
     simp_all [agrees8Positive] <;> omega
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8Positive]
   have hr : r = .Ok val := by
     cases r with
     | Ok v => simp_all
     | Err e => simp_all
   rw [hr] at r_post
   have hp : boundedScan 127 false (s.val.map UScalar.val) 0 cursor.val = .value (mag8Positive val) := by
     cases he : boundedScan 127 false (s.val.map UScalar.val) 0 cursor.val <;> simp_all [agrees8Positive,mag8Positive]
   have hd : digits.val = s.val++s1.val := by
     rw [s_post,s1_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   rw [←digits_post,hd,List.map_append,boundedScan_append,hp]
   have hslen : s.val.length=1 := s_post1
   simpa only [s1_post,i2_post,List.length_map,hslen] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8Positive]
   have hr : r = .Err v := by
     cases r with
     | Ok a => simp_all
     | Err a => simp_all
   rw [hr] at r_post
   have hd : digits.val = s.val++(digits.val.drop 1) := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   rw [←digits_post,hd,List.map_append,boundedScan_append,out_post]
   cases he : boundedScan 127 false (s.val.map UScalar.val) 0 cursor.val with
   | value n =>
     have hf : False := by simpa only [he,agrees8Positive] using r_post
     exact hf.elim
   | invalidDigit n => simpa only [he] using r_post
   | overflow n => simpa only [he] using r_post
   | underflow n => simpa only [he] using r_post


end LexicalScalarProofs
