import Wrapper
import Proofs.CountSpaces
open Aeneas Aeneas.Std Result
namespace unindent.Proofs
/-- Shared-reference delegation preserves the underlying implementation's result exactly. -/
theorem shared_unindent_eq {T O : Type} (inst : unindent.Unindent T O) (self : T) :
    Shared0T.Insts.UnindentUnindentUnindent.unindent inst self = inst.unindent self := by
  rfl
/-- Every successful underlying implementation remains successful through a shared reference. -/
theorem shared_unindent_spec {T O : Type} (inst : unindent.Unindent T O) (self : T)
    (post : O → Prop) (h : ∃ out, inst.unindent self = .ok out ∧ post out) :
    ∃ out, Shared0T.Insts.UnindentUnindentUnindent.unindent inst self = .ok out ∧ post out := by
  exact h
end unindent.Proofs
