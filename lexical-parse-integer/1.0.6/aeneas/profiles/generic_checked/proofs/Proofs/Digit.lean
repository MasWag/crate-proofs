import GenericScalar
import DigitSpecs
open Aeneas Aeneas.Std Result
namespace LexicalDigitProofs
open lexical_parse_integer_generic_harness
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def asciiRaw (c : Nat) : Nat :=
  if 48 ≤ c ∧ c ≤ 57 then c - 48
  else if 65 ≤ c ∧ c ≤ 90 then c - 65 + 10
  else if 97 ≤ c ∧ c ≤ 122 then c - 97 + 10
  else 255

theorem valid_digit_any (c : U8) (radix : U32) :
    lexical_util.digit.char_to_valid_digit_const c radix
      ⦃ d => d.val = if radix.val ≤ 10 then (c.val + 208) % 256 else asciiRaw c.val ⦄ := by
  unfold lexical_util.digit.char_to_valid_digit_const
  step*
  · rename_i hsmall
    have hs : radix.val ≤ 10 := by simpa using hsmall
    simp [hs, i_post,
      core.num.U8.wrapping_sub_val_eq, UScalar.ofNatCore_val_eq,
      U8.size_eq]
  · rename_i hlarge
    have hl : ¬ radix.val ≤ 10 := by simpa using hlarge
    simp only [hl, ite_false]
    split_ifs <;> step*
    all_goals simp [asciiRaw] at *
    all_goals split_ifs at *
    all_goals omega
private theorem asciiRaw_eq (c : Nat) :
    asciiRaw c = (LexicalParseIntegerDigitSpec.asciiValue c).getD 255 := by
  simp [asciiRaw, LexicalParseIntegerDigitSpec.asciiValue]
  split_ifs <;> rfl

private theorem digit_bridge (c radix : Nat)
    (hc : c < 256) (hr : 2 ≤ radix ∧ radix ≤ 36) :
    LexicalParseIntegerDigitSpec.digit radix c =
      let raw := if radix ≤ 10 then (c + 208) % 256 else asciiRaw c
      if raw < radix then some raw else none := by
  have hwrap : (c + 208) % 256 = if c < 48 then c + 208 else c - 48 := by
    by_cases hc48 : c < 48 <;> simp [hc48] <;> omega
  by_cases hsmall : radix ≤ 10
  · simp only [hsmall, ite_true, hwrap]
    by_cases hd : 48 ≤ c ∧ c ≤ 57
    · have hw : (if c < 48 then c + 208 else c - 48) = c - 48 := by simp [show ¬ c < 48 by omega]
      rw [hw]
      simp [LexicalParseIntegerDigitSpec.digit,
        LexicalParseIntegerDigitSpec.asciiValue, hd]
    · have hge : 10 ≤ if c < 48 then c + 208 else c - 48 := by
        split_ifs <;> omega
      have hnone : LexicalParseIntegerDigitSpec.digit radix c = none := by
        unfold LexicalParseIntegerDigitSpec.digit LexicalParseIntegerDigitSpec.asciiValue
        simp only [hd, ↓reduceIte]
        split_ifs <;> simp_all <;> omega
      rw [hnone]
      simp [show ¬(if c < 48 then c + 208 else c - 48) < radix by omega]
  · simp only [hsmall, ite_false]
    rw [asciiRaw_eq]
    cases hvalue : LexicalParseIntegerDigitSpec.asciiValue c with
    | none => simp [LexicalParseIntegerDigitSpec.digit, hvalue]; omega
    | some value => simp [LexicalParseIntegerDigitSpec.digit, hvalue]


unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun value _ hp => ⟨value, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

theorem char_to_digit_const_spec (c : U8) (radix : U32)
    (hr : 2 ≤ radix.val ∧ radix.val ≤ 36) :
    ∃ out, lexical_util.digit.char_to_digit_const c radix = .ok out ∧
      out.map (fun d => d.val) =
        LexicalParseIntegerDigitSpec.digit radix.val c.val := by
  obtain ⟨raw, hraw, hvalue⟩ := result_spec_success (valid_digit_any c radix)
  unfold lexical_util.digit.char_to_digit_const
  rw [hraw]
  simp only [bind_ok]
  have hmodel := digit_bridge c.val radix.val (by scalar_tac) hr
  by_cases hlt : raw.val < radix.val
  · have hlt' : raw < radix := hlt
    simp [hlt']
    rw [hmodel]
    rw [← hvalue]
    simp [hlt]
  · have hlt' : ¬raw < radix := hlt
    simp [hlt']
    rw [hmodel]
    rw [← hvalue]
    simp [hlt]

end LexicalDigitProofs
