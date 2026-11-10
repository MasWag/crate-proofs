import Proofs.U8
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem boundedScan_append (B : Nat) (negative : Bool) (a b : List Nat) (value index : Nat) :
 boundedScan B negative (a++b) value index =
 match boundedScan B negative a value index with
 | .value next => boundedScan B negative b next (index+a.length)
 | other => other := by
 induction a generalizing value index with
 | nil => simp [boundedScan]
 | cons c a ih =>
   cases hc : decimalDigit c with
   | none => simp [boundedScan,hc]
   | some d =>
     simp only [List.cons_append,boundedScan,hc,List.length_cons]
     split
     · rw [ih]
       simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
     · split <;> simp

@[step] theorem checked8_wp (bytes : Slice U8) (value : U8) (cursor : Usize)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_u8_from bytes value cursor ⦃ out => agrees8 out (boundedScan 255 false (bytes.val.map UScalar.val) value.val cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_u8_from_spec bytes value cursor hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem unchecked8_wp (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤2) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_u8_from bytes 0#u8 cursor ⦃ out => agrees8 out (boundedScan 255 false (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_u8_from_spec bytes cursor hlen hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

def agreesComplete8 (out : core.result.Result U8 lexical_util.error.Error) : CompleteResult → Prop
 | .empty i => match out with | .Err (.Empty j) => j.val=i | _ => False
 | .scanned result => agrees8 out result

@[step] theorem complete_u8_tail_spec (bytes : Slice U8) (cursor : Usize)
 (hc : cursor.val≤bytes.val.length) :
 complete_u8_from_cursor bytes cursor ⦃ out => agreesComplete8 out
   (if cursor.val=bytes.val.length then .empty cursor.val else
    .scanned (boundedScan 255 false ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val)) ⦄ := by
 unfold complete_u8_from_cursor
 step*
 · simp [Slice.len_val,agreesComplete8]
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8]
   simpa only [digits_post] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8]
   have hr : r = .Ok val := by
     cases r with
     | Ok v => simp_all
     | Err e => simp_all
   rw [hr] at r_post
   have hp : boundedScan 255 false (s.val.map UScalar.val) 0 cursor.val = .value val.val := by
     cases he : boundedScan 255 false (s.val.map UScalar.val) 0 cursor.val <;> simp_all [agrees8]
   have hd : digits.val = s.val++s1.val := by
     rw [s_post,s1_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 2 digits.val).symm
   rw [←digits_post,hd,List.map_append,boundedScan_append,hp]
   have hslen : s.val.length=2 := s_post1
   simpa only [s1_post,i2_post,List.length_map,hslen] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne,agreesComplete8]
   have hr : r = .Err v := by
     cases r with
     | Ok a => simp_all
     | Err a => simp_all
   rw [hr] at r_post
   have hd : digits.val = s.val++(digits.val.drop 2) := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 2 digits.val).symm
   rw [←digits_post,hd,List.map_append,boundedScan_append,out_post]
   cases he : boundedScan 255 false (s.val.map UScalar.val) 0 cursor.val with
   | value n =>
     have hf : False := by simpa only [he,agrees8] using r_post
     exact hf.elim
   | invalidDigit n => simpa only [he] using r_post
   | overflow n => simpa only [he] using r_post
   | underflow n => simpa only [he] using r_post


theorem complete_u8_spec (bytes : Slice U8) :
 complete_u8 bytes ⦃ out => agreesComplete8 out (completeU8 (bytes.val.map UScalar.val)) ⦄ := by
 unfold complete_u8
 step as ⟨b,hb⟩
 split
 · step*
   have hlen : bytes.val.length=0 := by
     have ht : b=true := by assumption
     rw [hb] at ht
     exact ht
   have hnil := List.eq_nil_of_length_eq_zero hlen
   simpa [hnil,completeU8] using out_post
 · have hn : bytes.val.length≠0 := by
     intro hlen
     have ht : b=true := by rw [hb]; exact hlen
     contradiction
   step as ⟨first,hfirst⟩
   split
   · step*
     cases he : bytes.val with
     | nil => simp_all
     | cons c rest =>
       simp only [he,List.getElem_cons_zero] at hfirst
       have hc : c=43#u8 := by grind
       cases rest <;> simpa [he,hc,completeU8] using out_post
   · step*
     cases he : bytes.val with
     | nil => simp_all
     | cons c rest =>
       simp only [he,List.getElem_cons_zero] at hfirst
       have hc : c.val≠43 := by
         intro hval
         have hscalar : c=43#u8 := UScalar.eq_of_val_eq (by simpa using hval)
         have hfirst43 : first=43#u8 := hfirst.trans hscalar
         contradiction
       simpa [he,completeU8,hc] using out_post

theorem complete_u8_success (bytes : Slice U8) :
 ∃ out, complete_u8 bytes = .ok out ∧
   agreesComplete8 out (completeU8 (bytes.val.map UScalar.val)) :=
 result_spec_success (complete_u8_spec bytes)

end LexicalScalarProofs