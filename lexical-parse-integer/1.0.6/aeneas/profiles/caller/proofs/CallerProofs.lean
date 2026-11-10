import LexicalParseIntegerCallerSafe
import Proofs.Decode
import Proofs.Validate
import CallerSpecs

open Aeneas Aeneas.Std Result

namespace CallerProofs

private theorem same_is4 (v : U32) :
    lexical_parse_integer_caller_harness.swar.is_4digits v =
      lexical_parse_integer_swar_harness.is_4digits v := by rfl

private theorem same_parse4 (v : U32) :
    lexical_parse_integer_caller_harness.swar.parse_4digits v =
      lexical_parse_integer_swar_harness.parse_4digits v := by rfl

private theorem same_is8 (v : U64) :
    lexical_parse_integer_caller_harness.swar.is_8digits v =
      lexical_parse_integer_swar_harness.is_8digits v := by rfl

private theorem same_parse8 (v : U64) :
    lexical_parse_integer_caller_harness.swar.parse_8digits v =
      lexical_parse_integer_swar_harness.parse_8digits v := by rfl

private theorem byteVal_lt (xs : List U8) (i : Nat) : CallerSpecs.byteVal xs i < 256 := by
  unfold CallerSpecs.byteVal
  scalar_tac

private theorem pack4_byte0 (xs : List U8) :
    LexicalParseIntegerSpec.byteAt (CallerSpecs.pack4 xs) 0 = CallerSpecs.byteVal xs 0 := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  unfold LexicalParseIntegerSpec.byteAt CallerSpecs.pack4
  norm_num
  omega

private theorem pack4_byte1 (xs : List U8) :
    LexicalParseIntegerSpec.byteAt (CallerSpecs.pack4 xs) 1 = CallerSpecs.byteVal xs 1 := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  unfold LexicalParseIntegerSpec.byteAt CallerSpecs.pack4
  norm_num
  omega

private theorem pack4_byte2 (xs : List U8) :
    LexicalParseIntegerSpec.byteAt (CallerSpecs.pack4 xs) 2 = CallerSpecs.byteVal xs 2 := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  unfold LexicalParseIntegerSpec.byteAt CallerSpecs.pack4
  norm_num
  omega

private theorem pack4_byte3 (xs : List U8) :
    LexicalParseIntegerSpec.byteAt (CallerSpecs.pack4 xs) 3 = CallerSpecs.byteVal xs 3 := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  unfold LexicalParseIntegerSpec.byteAt CallerSpecs.pack4
  norm_num
  omega

private theorem pack4_bound (xs : List U8) : CallerSpecs.pack4 xs < 2^32 := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  unfold CallerSpecs.pack4
  norm_num
  omega

private theorem pack4_digits (xs : List U8) (hlen : 4 ≤ xs.length) :
    LexicalParseIntegerSpec.decimal4Digits (CallerSpecs.pack4 xs) ↔
      CallerSpecs.block4Digits xs := by
  unfold LexicalParseIntegerSpec.decimal4Digits LexicalParseIntegerSpec.wordDigits
    CallerSpecs.block4Digits
  constructor
  · intro h
    refine ⟨hlen, ?_⟩
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst i; simpa [pack4_byte0] using h 0 (by omega)
    · subst i; simpa [pack4_byte1] using h 1 (by omega)
    · subst i; simpa [pack4_byte2] using h 2 (by omega)
    · subst i; simpa [pack4_byte3] using h 3 (by omega)
  · rintro ⟨_, h⟩ i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hcases with h0 | h1 | h2 | h3
    · subst i; simpa [pack4_byte0] using h 0 (by omega)
    · subst i; simpa [pack4_byte1] using h 1 (by omega)
    · subst i; simpa [pack4_byte2] using h 2 (by omega)
    · subst i; simpa [pack4_byte3] using h 3 (by omega)

private theorem pack4_value (xs : List U8) :
    LexicalParseIntegerSpec.decimal4Value (CallerSpecs.pack4 xs) =
      CallerSpecs.block4Value xs := by
  simp [LexicalParseIntegerSpec.decimal4Value,
    LexicalParseIntegerSpec.wordValue, CallerSpecs.block4Value,
    LexicalParseIntegerSpec.textValue, List.range_succ,
    pack4_byte0, pack4_byte1, pack4_byte2, pack4_byte3]

theorem try4_short (bytes : Slice U8) (cursor : Usize)
    (h : bytes.val.length < 4) :
    lexical_parse_integer_caller_harness.safe.try4 bytes cursor =
      .ok (none, cursor) := by
  simp [lexical_parse_integer_caller_harness.safe.try4, Slice.len, h]

theorem try8_short (bytes : Slice U8) (cursor : Usize)
    (h : bytes.val.length < 8) :
    lexical_parse_integer_caller_harness.safe.try8 bytes cursor =
      .ok (none, cursor) := by
  simp [lexical_parse_integer_caller_harness.safe.try8, Slice.len, h]

private theorem pack8_byte (xs : List U8) (i : Nat) (hi : i < 8) :
    LexicalParseIntegerSpec.byteAt (CallerSpecs.pack8 xs) i =
      CallerSpecs.byteVal xs i := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  have h4 := byteVal_lt xs 4
  have h5 := byteVal_lt xs 5
  have h6 := byteVal_lt xs 6
  have h7 := byteVal_lt xs 7
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc <;>
    subst i <;>
    norm_num [LexicalParseIntegerSpec.byteAt, CallerSpecs.pack8,
      CallerSpecs.pack4] <;> omega

private theorem pack8_bound (xs : List U8) : CallerSpecs.pack8 xs < 2^64 := by
  have h0 := byteVal_lt xs 0
  have h1 := byteVal_lt xs 1
  have h2 := byteVal_lt xs 2
  have h3 := byteVal_lt xs 3
  have h4 := byteVal_lt xs 4
  have h5 := byteVal_lt xs 5
  have h6 := byteVal_lt xs 6
  have h7 := byteVal_lt xs 7
  unfold CallerSpecs.pack8 CallerSpecs.pack4
  norm_num
  omega

private theorem pack8_digits (xs : List U8) (hlen : 8 ≤ xs.length) :
    LexicalParseIntegerSpec.decimal8Digits (CallerSpecs.pack8 xs) ↔
      CallerSpecs.block8Digits xs := by
  unfold LexicalParseIntegerSpec.decimal8Digits LexicalParseIntegerSpec.wordDigits
    CallerSpecs.block8Digits
  constructor
  · intro h
    refine ⟨hlen, ?_⟩
    intro i hi
    simpa [pack8_byte xs i hi] using h i hi
  · rintro ⟨_, h⟩ i hi
    simpa [pack8_byte xs i hi] using h i hi

private theorem pack8_value (xs : List U8) :
    LexicalParseIntegerSpec.decimal8Value (CallerSpecs.pack8 xs) =
      CallerSpecs.block8Value xs := by
  simp [LexicalParseIntegerSpec.decimal8Value,
    LexicalParseIntegerSpec.wordValue, CallerSpecs.block8Value,
    LexicalParseIntegerSpec.textValue, List.range_succ,
    pack8_byte]

private theorem try4_long_spec (bytes : Slice U8) (cursor : Usize)
    (hlen : 4 ≤ bytes.val.length)
    (hcursor : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, lexical_parse_integer_caller_harness.safe.try4 bytes cursor = .ok out ∧
      (CallerSpecs.block4Digits bytes.val ↔ out.1.isSome) ∧
      (CallerSpecs.block4Digits bytes.val →
        ∃ v, out.1 = some v ∧ v.val = CallerSpecs.block4Value bytes.val ∧
          out.2.val = cursor.val + 4) ∧
      (¬CallerSpecs.block4Digits bytes.val → out = (none, cursor)) := by
  obtain ⟨out, hout, hpost⟩ := LexicalParseIntegerProofs.result_spec_success
    (p := fun out =>
      (CallerSpecs.block4Digits bytes.val ↔ out.1.isSome) ∧
      (CallerSpecs.block4Digits bytes.val →
        ∃ v, out.1 = some v ∧ v.val = CallerSpecs.block4Value bytes.val ∧
          out.2.val = cursor.val + 4) ∧
      (¬CallerSpecs.block4Digits bytes.val → out = (none, cursor)))
    (m := lexical_parse_integer_caller_harness.safe.try4 bytes cursor) (by
      unfold lexical_parse_integer_caller_harness.safe.try4
      step*
      have hword : word.val = CallerSpecs.pack4 bytes.val := by
        have h0 : (bytes.val[0]?.getD 0#u8) = bytes.val[0] := by
          simp [List.getElem?_eq_getElem (by omega : 0 < bytes.val.length)]
        have h1 : (bytes.val[1]?.getD 0#u8) = bytes.val[1] := by
          simp [List.getElem?_eq_getElem (by omega : 1 < bytes.val.length)]
        have h2 : (bytes.val[2]?.getD 0#u8) = bytes.val[2] := by
          simp [List.getElem?_eq_getElem (by omega : 2 < bytes.val.length)]
        have h3 : (bytes.val[3]?.getD 0#u8) = bytes.val[3] := by
          simp [List.getElem?_eq_getElem (by omega : 3 < bytes.val.length)]
        have hb0 := byteVal_lt bytes.val 0
        have hb1 := byteVal_lt bytes.val 1
        have hb2 := byteVal_lt bytes.val 2
        have hb3 := byteVal_lt bytes.val 3
        simp only [CallerSpecs.byteVal, h0] at hb0
        simp only [CallerSpecs.byteVal, h1] at hb1
        simp only [CallerSpecs.byteVal, h2] at hb2
        simp only [CallerSpecs.byteVal, h3] at hb3
        simp only [word_post, i10_post, i6_post, i2_post, i4_post,
          i8_post, i12_post, i1_post, i3_post, i7_post, i11_post,
          i5_post, i9_post, i13_post]
        simp [CallerSpecs.pack4, CallerSpecs.byteVal, Nat.shiftLeft_eq,
          U32.size_eq, h0, h1, h2, h3]
        omega
      obtain ⟨b, hb, hspec⟩ := LexicalParseIntegerProofs.is4_decimal word
      rw [← same_is4] at hb
      simp only [hb, bind_ok]
      have hblock : b = true ↔ CallerSpecs.block4Digits bytes.val := by
        rw [← pack4_digits bytes.val hlen, ← hword]
        exact hspec
      by_cases hbool : b = true
      · have hd : LexicalParseIntegerSpec.decimal4Digits word.val :=
          hspec.mp hbool
        obtain ⟨parsed, hparse, hvalue⟩ :=
          LexicalParseIntegerProofs.parse4_decimal_success word hd
        rw [← same_parse4] at hparse
        simp [hbool, hparse]
        step*
        have hb' := hblock.mp hbool
        refine ⟨?_, ?_, ?_⟩
        · simpa using hb'
        · intro _
          refine ⟨parsed, rfl, ?_, i15_post⟩
          rw [← pack4_value bytes.val, ← hword]
          exact hvalue
        · simp [hb']
      · have hn : ¬CallerSpecs.block4Digits bytes.val :=
          fun hh => hbool (hblock.mpr hh)
        simp [hbool, hn])
  exact ⟨out, hout, hpost⟩

private theorem try8_long_spec (bytes : Slice U8) (cursor : Usize)
    (hlen : 8 ≤ bytes.val.length)
    (hcursor : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, lexical_parse_integer_caller_harness.safe.try8 bytes cursor = .ok out ∧
      (CallerSpecs.block8Digits bytes.val ↔ out.1.isSome) ∧
      (CallerSpecs.block8Digits bytes.val →
        ∃ v, out.1 = some v ∧ v.val = CallerSpecs.block8Value bytes.val ∧
          out.2.val = cursor.val + 8) ∧
      (¬CallerSpecs.block8Digits bytes.val → out = (none, cursor)) := by
  obtain ⟨out, hout, hpost⟩ := LexicalParseIntegerProofs.result_spec_success
    (p := fun out =>
      (CallerSpecs.block8Digits bytes.val ↔ out.1.isSome) ∧
      (CallerSpecs.block8Digits bytes.val →
        ∃ v, out.1 = some v ∧ v.val = CallerSpecs.block8Value bytes.val ∧
          out.2.val = cursor.val + 8) ∧
      (¬CallerSpecs.block8Digits bytes.val → out = (none, cursor)))
    (m := lexical_parse_integer_caller_harness.safe.try8 bytes cursor) (by
      unfold lexical_parse_integer_caller_harness.safe.try8
      step*
      have hword : word.val = CallerSpecs.pack8 bytes.val := by
        have h0 : (bytes.val[0]?.getD 0#u8) = bytes.val[0] := by
          simp [List.getElem?_eq_getElem (by omega : 0 < bytes.val.length)]
        have h1 : (bytes.val[1]?.getD 0#u8) = bytes.val[1] := by
          simp [List.getElem?_eq_getElem (by omega : 1 < bytes.val.length)]
        have h2 : (bytes.val[2]?.getD 0#u8) = bytes.val[2] := by
          simp [List.getElem?_eq_getElem (by omega : 2 < bytes.val.length)]
        have h3 : (bytes.val[3]?.getD 0#u8) = bytes.val[3] := by
          simp [List.getElem?_eq_getElem (by omega : 3 < bytes.val.length)]
        have h4 : (bytes.val[4]?.getD 0#u8) = bytes.val[4] := by
          simp [List.getElem?_eq_getElem (by omega : 4 < bytes.val.length)]
        have h5 : (bytes.val[5]?.getD 0#u8) = bytes.val[5] := by
          simp [List.getElem?_eq_getElem (by omega : 5 < bytes.val.length)]
        have h6 : (bytes.val[6]?.getD 0#u8) = bytes.val[6] := by
          simp [List.getElem?_eq_getElem (by omega : 6 < bytes.val.length)]
        have h7 : (bytes.val[7]?.getD 0#u8) = bytes.val[7] := by
          simp [List.getElem?_eq_getElem (by omega : 7 < bytes.val.length)]
        have hb0 := byteVal_lt bytes.val 0
        have hb1 := byteVal_lt bytes.val 1
        have hb2 := byteVal_lt bytes.val 2
        have hb3 := byteVal_lt bytes.val 3
        have hb4 := byteVal_lt bytes.val 4
        have hb5 := byteVal_lt bytes.val 5
        have hb6 := byteVal_lt bytes.val 6
        have hb7 := byteVal_lt bytes.val 7
        simp only [CallerSpecs.byteVal, h0] at hb0
        simp only [CallerSpecs.byteVal, h1] at hb1
        simp only [CallerSpecs.byteVal, h2] at hb2
        simp only [CallerSpecs.byteVal, h3] at hb3
        simp only [CallerSpecs.byteVal, h4] at hb4
        simp only [CallerSpecs.byteVal, h5] at hb5
        simp only [CallerSpecs.byteVal, h6] at hb6
        simp only [CallerSpecs.byteVal, h7] at hb7
        simp only [word_post, i26_post, i22_post, i18_post, i14_post,
          i10_post, i6_post, i2_post, i4_post, i8_post, i12_post,
          i16_post, i20_post, i24_post, i28_post,
          i1_post, i3_post, i7_post, i11_post, i15_post,
          i19_post, i23_post, i27_post,
          i5_post, i9_post, i13_post, i17_post, i21_post,
          i25_post, i29_post]
        simp [CallerSpecs.pack8, CallerSpecs.pack4, CallerSpecs.byteVal,
          Nat.shiftLeft_eq, U64.size_eq,
          h0, h1, h2, h3, h4, h5, h6, h7]
        omega
      obtain ⟨b, hb, hspec⟩ := LexicalParseIntegerProofs.is8_decimal word
      rw [← same_is8] at hb
      simp only [hb, bind_ok]
      have hblock : b = true ↔ CallerSpecs.block8Digits bytes.val := by
        rw [← pack8_digits bytes.val hlen, ← hword]
        exact hspec
      by_cases hbool : b = true
      · have hd : LexicalParseIntegerSpec.decimal8Digits word.val :=
          hspec.mp hbool
        obtain ⟨parsed, hparse, hvalue⟩ :=
          LexicalParseIntegerProofs.parse8_decimal_success word hd
        rw [← same_parse8] at hparse
        simp [hbool, hparse]
        step*
        have hb' := hblock.mp hbool
        refine ⟨?_, ?_, ?_⟩
        · simpa using hb'
        · intro _
          refine ⟨parsed, rfl, ?_, i31_post⟩
          rw [← pack8_value bytes.val, ← hword]
          exact hvalue
        · simp [hb']
      · have hn : ¬CallerSpecs.block8Digits bytes.val :=
          fun hh => hbool (hblock.mpr hh)
        simp [hbool, hn])
  exact ⟨out, hout, hpost⟩

theorem try4_contract (bytes : Slice U8) (cursor : Usize)
    (hcursor : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, lexical_parse_integer_caller_harness.safe.try4 bytes cursor = .ok out ∧
      (CallerSpecs.block4Digits bytes.val ↔ out.1.isSome) ∧
      (CallerSpecs.block4Digits bytes.val →
        ∃ v, out.1 = some v ∧ v.val = CallerSpecs.block4Value bytes.val ∧
          out.2.val = cursor.val + 4) ∧
      (¬CallerSpecs.block4Digits bytes.val → out = (none, cursor)) := by
  by_cases hlen : 4 ≤ bytes.val.length
  · exact try4_long_spec bytes cursor hlen hcursor
  · have hshort : bytes.val.length < 4 := by omega
    refine ⟨(none, cursor), try4_short bytes cursor hshort, ?_⟩
    simp [CallerSpecs.block4Digits, hlen]

theorem try8_contract (bytes : Slice U8) (cursor : Usize)
    (hcursor : cursor.val + bytes.val.length ≤ Usize.max) :
    ∃ out, lexical_parse_integer_caller_harness.safe.try8 bytes cursor = .ok out ∧
      (CallerSpecs.block8Digits bytes.val ↔ out.1.isSome) ∧
      (CallerSpecs.block8Digits bytes.val →
        ∃ v, out.1 = some v ∧ v.val = CallerSpecs.block8Value bytes.val ∧
          out.2.val = cursor.val + 8) ∧
      (¬CallerSpecs.block8Digits bytes.val → out = (none, cursor)) := by
  by_cases hlen : 8 ≤ bytes.val.length
  · exact try8_long_spec bytes cursor hlen hcursor
  · have hshort : bytes.val.length < 8 := by omega
    refine ⟨(none, cursor), try8_short bytes cursor hshort, ?_⟩
    simp [CallerSpecs.block8Digits, hlen]

end CallerProofs
