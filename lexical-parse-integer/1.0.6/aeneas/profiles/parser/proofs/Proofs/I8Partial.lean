import Proofs.I8Front
import Proofs.Partial
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def signedMagnitude (neg : Bool) (v : Int) : Nat := if neg then (-v).toNat else v.toNat
@[simp] theorem signedMagnitude_value (neg : Bool) (v : Nat) : signedMagnitude neg (signedValue neg v)=v := by
 cases neg <;> simp [signedMagnitude,signedValue]

theorem signedPartialScan_append (B : Nat) (neg : Bool) (a b : List Nat) (value index : Nat) :
 signedPartialScan B neg (a++b) value index =
 match signedPartialScan B neg a value index with
 | .value next j => if j < index+a.length then .value next j else signedPartialScan B neg b (signedMagnitude neg next) j
 | other => other := by
 induction a generalizing value index with
 | nil => simp [signedPartialScan]
 | cons c a ih =>
   cases hc : decimalDigit c with
   | none => simp [signedPartialScan,hc]
   | some d =>
     simp only [List.cons_append,signedPartialScan,hc,List.length_cons]
     split
     · rw [ih]; simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
     · cases neg <;> rfl

theorem signedPartialScan_le (B : Nat) (neg : Bool) (a : List Nat) (value index : Nat) (next : Int) (j : Nat)
 (h : signedPartialScan B neg a value index = .value next j) : j ≤ index+a.length := by
 induction a generalizing value index with
 | nil => simp only [signedPartialScan,SignedPartialResult.value.injEq] at h; omega
 | cons c a ih =>
   simp only [signedPartialScan] at h
   cases hc : decimalDigit c with
   | none => simp only [hc,SignedPartialResult.value.injEq] at h; simp; omega
   | some d =>
     simp only [hc] at h
     split at h
     · have hh := ih _ _ h; simp only [List.length_cons]; omega
     · cases neg <;> contradiction

theorem signedPartialScan_sign (B : Nat) (neg : Bool) (a : List Nat) (value index : Nat) (next : Int) (j : Nat)
 (h : signedPartialScan B neg a value index = .value next j) : if neg then next≤0 else 0≤next := by
 induction a generalizing value index with
 | nil => simp only [signedPartialScan,SignedPartialResult.value.injEq] at h; rcases h with ⟨rfl,rfl⟩; cases neg <;> simp [signedValue]
 | cons c a ih =>
   simp only [signedPartialScan] at h
   cases hc : decimalDigit c with
   | none => simp only [hc,SignedPartialResult.value.injEq] at h; rcases h with ⟨rfl,rfl⟩; cases neg <;> simp [signedValue]
   | some d =>
     simp only [hc] at h
     split at h
     · exact ih _ _ h
     · cases neg <;> contradiction


@[step] theorem partial_checked8Negative_wp (bytes : Slice U8) (value : I8) (cursor : Usize)
 (hv : value.val≤0) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_i8_negative_partial_from bytes value cursor ⦃ out => agreesSignedPartial out (signedPartialScan 128 true (bytes.val.map UScalar.val) (mag8Negative value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i8_negative_partial_from_spec bytes value cursor hv hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem partial_unchecked8Negative_wp (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤1) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i8_negative_partial_from bytes 0#i8 cursor ⦃ out => agreesSignedPartial out (signedPartialScan 128 true (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i8_negative_partial_from_spec bytes cursor hlen hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost
@[step] theorem partial_i8_negative_tail_spec (bytes : Slice U8) (cursor : Usize)
 (hc : cursor.val≤bytes.val.length) :
 partial_i8_negative_from_cursor bytes cursor ⦃ out => agreesSignedPartial out
   (if cursor.val=bytes.val.length then .empty cursor.val else
    signedPartialScan 128 true ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val) ⦄ := by
 unfold partial_i8_negative_from_cursor
 step*
 · simp [agreesSignedPartial]
 · rcases val with ⟨value,ended⟩
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   have hr : r = .Ok (value,ended) := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : signedPartialScan 128 true (s.val.map UScalar.val) 0 cursor.val = .value value.val ended.val := by
     cases he : signedPartialScan 128 true (s.val.map UScalar.val) 0 cursor.val <;> simp_all [agreesSignedPartial]
   have hslen : s.val.length=1 := s_post1
   have hle := signedPartialScan_le 128 true (s.val.map UScalar.val) 0 cursor.val value.val ended.val hp
   simp only [List.length_map,hslen] at hle
   have hd : digits.val = s.val++digits.val.drop 1 := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   simp only [if_neg hne]
   step*
   · rw [←digits_post,hd,List.map_append,signedPartialScan_append,hp]
     simp only [List.length_map,hslen]
     have hlt : ended.val < i2.val := by
       have h : ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     rw [if_pos (by omega)]
     exact ⟨rfl,rfl⟩
   · have hsign := signedPartialScan_sign 128 true (s.val.map UScalar.val) 0 cursor.val value.val ended.val hp
     simpa using hsign
   · rw [←digits_post,hd,List.map_append,signedPartialScan_append,hp]
     simp only [List.length_map,hslen]
     have hnlt : ¬ended.val < i2.val := by
       have h : ¬ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     have hend : ended.val=cursor.val+1 := by omega
     rw [if_neg (by omega)]
     simpa only [s1_post,i2_post,hend,signedMagnitude,ite_true,mag8Negative] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r = .Err v := by cases r <;> simp_all
   rw [hr] at r_post
   have hd : digits.val = s.val++digits.val.drop 1 := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   rw [←digits_post,hd,List.map_append,signedPartialScan_append,out_post]
   cases he : signedPartialScan 128 true (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agreesSignedPartial] using r_post
     exact hf.elim
   | overflow n => simpa only [he] using r_post
   | underflow n => simpa only [he] using r_post
   | empty n => simpa only [he] using r_post


@[step] theorem partial_checked8Positive_wp (bytes : Slice U8) (value : I8) (cursor : Usize)
 (hv : 0≤value.val) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_i8_positive_partial_from bytes value cursor ⦃ out => agreesSignedPartial out (signedPartialScan 127 false (bytes.val.map UScalar.val) (mag8Positive value) cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_i8_positive_partial_from_spec bytes value cursor hv hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem partial_unchecked8Positive_wp (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤1) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_i8_positive_partial_from bytes 0#i8 cursor ⦃ out => agreesSignedPartial out (signedPartialScan 127 false (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_i8_positive_partial_from_spec bytes cursor hlen hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost
@[step] theorem partial_i8_positive_tail_spec (bytes : Slice U8) (cursor : Usize)
 (hc : cursor.val≤bytes.val.length) :
 partial_i8_positive_from_cursor bytes cursor ⦃ out => agreesSignedPartial out
   (if cursor.val=bytes.val.length then .empty cursor.val else
    signedPartialScan 127 false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val) ⦄ := by
 unfold partial_i8_positive_from_cursor
 step*
 · simp [agreesSignedPartial]
 · rcases val with ⟨value,ended⟩
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   have hr : r = .Ok (value,ended) := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : signedPartialScan 127 false (s.val.map UScalar.val) 0 cursor.val = .value value.val ended.val := by
     cases he : signedPartialScan 127 false (s.val.map UScalar.val) 0 cursor.val <;> simp_all [agreesSignedPartial]
   have hslen : s.val.length=1 := s_post1
   have hle := signedPartialScan_le 127 false (s.val.map UScalar.val) 0 cursor.val value.val ended.val hp
   simp only [List.length_map,hslen] at hle
   have hd : digits.val = s.val++digits.val.drop 1 := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   simp only [if_neg hne]
   step*
   · rw [←digits_post,hd,List.map_append,signedPartialScan_append,hp]
     simp only [List.length_map,hslen]
     have hlt : ended.val < i2.val := by
       have h : ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     rw [if_pos (by omega)]
     exact ⟨rfl,rfl⟩
   · have hsign := signedPartialScan_sign 127 false (s.val.map UScalar.val) 0 cursor.val value.val ended.val hp
     simpa using hsign
   · rw [←digits_post,hd,List.map_append,signedPartialScan_append,hp]
     simp only [List.length_map,hslen]
     have hnlt : ¬ended.val < i2.val := by
       have h : ¬ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     have hend : ended.val=cursor.val+1 := by omega
     rw [if_neg (by omega)]
     simpa only [s1_post,i2_post,hend,signedMagnitude,Bool.false_eq_true,ite_false,mag8Positive] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r = .Err v := by cases r <;> simp_all
   rw [hr] at r_post
   have hd : digits.val = s.val++digits.val.drop 1 := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 1 digits.val).symm
   rw [←digits_post,hd,List.map_append,signedPartialScan_append,out_post]
   cases he : signedPartialScan 127 false (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agreesSignedPartial] using r_post
     exact hf.elim
   | overflow n => simpa only [he] using r_post
   | underflow n => simpa only [he] using r_post
   | empty n => simpa only [he] using r_post



theorem partial_after_sign (bytes : Slice U8) (cursor : Usize) (negative : Bool)
 (hc : cursor.val≤bytes.val.length)
 (hm : signedInput (bytes.val.map UScalar.val) = ((bytes.val.map UScalar.val).drop cursor.val,cursor.val,negative)) :
 partialI8 (bytes.val.map UScalar.val) =
 (if cursor.val=bytes.val.length then .empty cursor.val else
 signedPartialScan (if negative then 128 else 127) negative ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val) := by
 unfold partialI8
 rw [hm]
 by_cases he : cursor.val=bytes.val.length
 · simp [he]
 · have hn : bytes.val.drop cursor.val ≠ [] := by
     intro h
     have hl := congrArg List.length h
     simp only [List.length_drop,List.length_nil] at hl
     omega
   cases hd : bytes.val.drop cursor.val with
   | nil => contradiction
   | cons a rest => simp [←List.map_drop,hd,he]

theorem partial_i8_spec (bytes : Slice U8) :
 partial_i8 bytes ⦃ out => agreesSignedPartial out (partialI8 (bytes.val.map UScalar.val)) ⦄ := by
 unfold partial_i8
 step*
 · rw [partial_after_sign bytes cursor negative negative_post negative_post1]
   have hn : negative=true := by assumption
   simpa [hn] using out_post
 · rw [partial_after_sign bytes cursor negative negative_post negative_post1]
   have hn : negative=false := by cases negative <;> simp_all
   simpa [hn] using out_post

theorem partial_i8_success (bytes : Slice U8) :
 ∃ out, partial_i8 bytes = .ok out ∧ agreesSignedPartial out (partialI8 (bytes.val.map UScalar.val)) :=
 result_spec_success (partial_i8_spec bytes)
#print axioms partial_i8_success
end LexicalScalarProofs
