import Specs

/-! Shared helpers for the adapted proofs: total WP to total success, and
byte-list views of generated slices. -/

open Aeneas Aeneas.Std Aeneas.Std.WP
open JsonptrSpecModel JsonptrAdaptedSpec

namespace JsonptrAdaptedProofs

theorem ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = .ok x ∧ P x := by
  cases hm : m with
  | ret out => exact ⟨out, rfl, (spec_ok out).mp (hm ▸ h)⟩
  | div => exact False.elim (spec_div.mp (hm ▸ h))
  | vis e k => exact False.elim ((spec_vis e k).mp (hm ▸ h))

/-- The first position in `l` whose byte satisfies `p`, if any. -/
def FirstIdx (p : U8 → Prop) (l : List U8) : Option Usize → Prop
  | none => ∀ (k : Nat) x, l[k]? = some x → ¬ p x
  | some j => (∃ x, l[j.val]? = some x ∧ p x) ∧ ∀ (k : Nat) x, k < j.val → l[k]? = some x → ¬ p x

@[simp] theorem bytes_length (s : Slice U8) : (bytes s).length = s.length := by
  simp [bytes]

theorem bytes_getElem (s : Slice U8) (k : Nat) (hk : k < (bytes s).length) :
    (bytes s)[k] = (s.val[k]'(by simpa using hk)).val := by
  simp [bytes]

end JsonptrAdaptedProofs
