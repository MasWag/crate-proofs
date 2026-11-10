import Proofs.PartialLoops
open Aeneas Aeneas.Std Result
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem partialScan_append (B : Nat) (a b : List Nat) (value index : Nat) :
 partialScan B (a++b) value index =
 match partialScan B a value index with
 | .value next j => if j < index+a.length then .value next j else partialScan B b next j
 | other => other := by
 induction a generalizing value index with
 | nil => simp [partialScan]
 | cons c a ih =>
   cases hc : decimalDigit c with
   | none => simp [partialScan,hc]
   | some d =>
     simp only [List.cons_append,partialScan,hc,List.length_cons]
     split
     · rw [ih]
       simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
     · rfl

theorem partialScan_le (B : Nat) (a : List Nat) (value index next j : Nat)
 (h : partialScan B a value index = .value next j) : j ≤ index+a.length := by
 induction a generalizing value index with
 | nil => simp only [partialScan,PartialResult.value.injEq] at h; omega
 | cons c a ih =>
   simp only [partialScan] at h
   cases hc : decimalDigit c with
   | none => simp only [hc,PartialResult.value.injEq] at h; simp; omega
   | some d =>
     simp only [hc] at h
     split at h
     · have hh := ih _ _ h
       simp only [List.length_cons]
       omega
     · contradiction

@[step] theorem partial_checked8_wp (bytes : Slice U8) (value : U8) (cursor : Usize)
 (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 checked_u8_partial_from bytes value cursor ⦃ out => agreesPartial out (partialScan 255 (bytes.val.map UScalar.val) value.val cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := checked_u8_partial_from_spec bytes value cursor hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem partial_unchecked8_wp (bytes : Slice U8) (cursor : Usize)
 (hlen : bytes.val.length≤2) (hsafe : cursor.val+bytes.val.length≤Usize.max) :
 unchecked_u8_partial_from bytes 0#u8 cursor ⦃ out => agreesPartial out (partialScan 255 (bytes.val.map UScalar.val) 0 cursor.val) ⦄ := by
 obtain ⟨out,heq,hpost⟩ := unchecked_u8_partial_from_spec bytes cursor hlen hsafe
 rw [heq]
 simpa only [WP.spec_ok] using hpost

@[step] theorem partial_u8_tail_spec (bytes : Slice U8) (cursor : Usize)
 (hc : cursor.val≤bytes.val.length) :
 partial_u8_from_cursor bytes cursor ⦃ out => agreesPartial out
   (if cursor.val=bytes.val.length then .empty cursor.val else
    partialScan 255 ((bytes.val.drop cursor.val).map UScalar.val) 0 cursor.val) ⦄ := by
 unfold partial_u8_from_cursor
 step*
 · simp [agreesPartial]
 · rcases val with ⟨value,ended⟩
   have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   have hr : r = .Ok (value,ended) := by cases r <;> simp_all
   rw [hr] at r_post
   have hp : partialScan 255 (s.val.map UScalar.val) 0 cursor.val = .value value.val ended.val := by
     cases he : partialScan 255 (s.val.map UScalar.val) 0 cursor.val <;> simp_all [agreesPartial]
   have hslen : s.val.length=2 := s_post1
   have hle := partialScan_le 255 (s.val.map UScalar.val) 0 cursor.val value.val ended.val hp
   simp only [List.length_map,hslen] at hle
   have hd : digits.val = s.val++digits.val.drop 2 := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 2 digits.val).symm
   simp only [if_neg hne]
   step*
   · rw [←digits_post,hd,List.map_append,partialScan_append,hp]
     simp only [List.length_map,hslen]
     have hlt : ended.val < i2.val := by
       have h : ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     rw [if_pos (by omega)]
     exact ⟨rfl,rfl⟩
   · rw [←digits_post,hd,List.map_append,partialScan_append,hp]
     simp only [List.length_map,hslen]
     have hnlt : ¬ended.val < i2.val := by
       have h : ¬ended < i2 := by assumption
       simpa only [UScalar.lt_equiv] using h
     have hend : ended.val=cursor.val+2 := by omega
     rw [if_neg (by omega)]
     simpa only [s1_post,i2_post,hend] using out_post
 · have hne : cursor.val≠bytes.val.length := by
     intro he
     have heq : cursor=bytes.len := UScalar.eq_of_val_eq (by simpa [Slice.len_val] using he)
     contradiction
   simp only [if_neg hne]
   have hr : r = .Err v := by cases r <;> simp_all
   rw [hr] at r_post
   have hd : digits.val = s.val++digits.val.drop 2 := by
     rw [s_post]
     simp only [List.slice,List.drop_zero]
     exact (List.take_append_drop 2 digits.val).symm
   rw [←digits_post,hd,List.map_append,partialScan_append,out_post]
   cases he : partialScan 255 (s.val.map UScalar.val) 0 cursor.val with
   | value n j =>
     have hf : False := by simpa only [he,agreesPartial] using r_post
     exact hf.elim
   | overflow n => simpa only [he] using r_post
   | empty n => simpa only [he] using r_post

theorem partial_u8_spec (bytes : Slice U8) :
 partial_u8 bytes ⦃ out => agreesPartial out (partialU8 (bytes.val.map UScalar.val)) ⦄ := by
 unfold partial_u8
 step as ⟨b,hb⟩
 split
 · step*
   have hlen : bytes.val.length=0 := by
     have ht : b=true := by assumption
     rw [hb] at ht
     exact ht
   have hnil := List.eq_nil_of_length_eq_zero hlen
   simpa [hnil,partialU8] using out_post
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
       cases rest <;> simpa [he,hc,partialU8] using out_post
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
       simpa [he,partialU8,hc] using out_post

theorem partial_u8_success (bytes : Slice U8) :
 ∃ out, partial_u8 bytes = .ok out ∧
   agreesPartial out (partialU8 (bytes.val.map UScalar.val)) :=
 result_spec_success (partial_u8_spec bytes)

end LexicalScalarProofs