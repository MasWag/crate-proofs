import Sign
import SignSpecs
open Aeneas Aeneas.Std Result
namespace LexicalParseIntegerSignProofs
open lexical_parse_integer_sign_harness LexicalParseIntegerSignSpec

def observed (out : core.result.Result Bool lexical_util.error.Error × Usize)
    (cursor : Usize) (spec : SignResult) : Prop :=
  match spec with
  | .accepted neg cursor => out.1 = .Ok neg ∧ out.2.val = cursor
  | .invalidPositiveSign index =>
      out.1 = .Err (.InvalidPositiveSign cursor) ∧ out.2.val = index
  | .missingSign index =>
      out.1 = .Err (.MissingSign cursor) ∧ out.2.val = index

unseal Result in
private theorem result_spec_success {α : Type} {m : Result α} {p : α → Prop}
    (h : m ⦃ out => p out ⦄) : ∃ out, m = Result.ok out ∧ p out := by
  unfold Aeneas.Std.WP.spec at h
  exact h.induction (P := fun t _ => ∃ out, t = Result.ok out ∧ p out)
    (fun value _ hp => ⟨value, rfl, hp⟩)
    (fun effect _ _ hfalse => False.elim hfalse)

private theorem advance (cursor : Usize) (hsafe : cursor.val < Usize.max) :
    ∃ next : Usize, (cursor + 1#usize : Result Usize) = Result.ok next ∧ next.val = cursor.val + 1 := by
  have hmax : cursor.val + (1#usize).val ≤ Usize.max := by scalar_tac
  exact result_spec_success (Usize.add_spec hmax)

theorem sign_spec (byte : Option U8) (cursor : Usize)
    (signed noPositive required : Bool)
    (hsafe : (byte = some 43#u8 ∧ ¬noPositive ∨ byte = some 45#u8 ∧ signed) →
      cursor.val < Usize.max) :
    ∃ out, parse_sign_state byte cursor signed noPositive required = .ok out ∧
      observed out cursor (parseSign (byte.map UScalar.val) cursor.val signed noPositive required) := by
  cases byte with
  | none =>
      cases required <;> simp [parse_sign_state, parseSign, observed]
  | some c =>
      by_cases hp : c = 43#u8
      · subst c
        cases noPositive with
        | false =>
          obtain ⟨next, hadd, hval⟩ := advance cursor (hsafe (Or.inl ⟨rfl, by decide⟩))
          refine ⟨(.Ok false, next), ?_, ?_⟩
          · simp [parse_sign_state, hadd] <;> rfl
          · simp [parseSign, observed, hval]
        | true =>
          refine ⟨(.Err (.InvalidPositiveSign cursor), cursor), ?_, ?_⟩
          · rfl
          · simp [parseSign, observed]
      · by_cases hm : c = 45#u8
        · subst c
          cases signed with
          | false =>
            cases required with
            | false =>
              refine ⟨(.Ok false, cursor), ?_, ?_⟩
              · rfl
              · simp [parseSign, observed]
            | true =>
              refine ⟨(.Err (.MissingSign cursor), cursor), ?_, ?_⟩
              · rfl
              · simp [parseSign, observed]
          | true =>
            obtain ⟨next, hadd, hval⟩ := advance cursor (hsafe (Or.inr ⟨rfl, by decide⟩))
            refine ⟨(.Ok true, next), ?_, ?_⟩
            · simp [parse_sign_state, hadd] <;> rfl
            · simp [parseSign, observed, hval]
        · have h43 : c.val ≠ 43 := by
            intro h
            exact hp (UScalar.eq_of_val_eq (by simpa using h))
          have h45 : c.val ≠ 45 := by
            intro h
            exact hm (UScalar.eq_of_val_eq (by simpa using h))
          cases required with
          | false =>
            refine ⟨(.Ok false, cursor), ?_, ?_⟩
            · simp [parse_sign_state, hp, hm] <;> split <;> first | exact False.elim (h43 (by rfl)) | exact False.elim (h45 (by rfl)) | rfl
            · simp [parseSign, observed, h43, h45]
          | true =>
            refine ⟨(.Err (.MissingSign cursor), cursor), ?_, ?_⟩
            · simp [parse_sign_state, hp, hm] <;> split <;> first | exact False.elim (h43 (by rfl)) | exact False.elim (h45 (by rfl)) | rfl
            · simp [parseSign, observed, h43, h45]
