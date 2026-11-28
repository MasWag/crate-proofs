import LebErrorDefaults

open Aeneas Aeneas.Std Result

namespace leb128fmt_error_defaults

open leb128fmt

theorem clone_from_spec (destination source : leb128fmt.Error) :
    clone_from destination source = ok source := by
  cases source <;>
    simp [clone_from, core.clone.Clone.clone_from.default,
      Error.Insts.CoreCloneClone.clone, InnerError.Insts.CoreCloneClone.clone]

theorem not_equal_spec (left right : leb128fmt.Error) :
    ∃ unequal, not_equal left right = ok unequal ∧ (unequal = true ↔ left ≠ right) := by
  rcases left with _ | _ <;> rcases right with _ | _
  all_goals
    simp [not_equal, core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      Error.Insts.CoreCmpPartialEqError.eq,
      InnerError.Insts.CoreCmpPartialEqInnerError.eq, InnerError.read_discriminant]

theorem assert_receiver_is_total_eq_spec (error : leb128fmt.Error) :
    assert_receiver_is_total_eq error = ok () := by
  rfl

theorem description_spec (error : leb128fmt.Error) :
    description error = ok (toStr "description() is deprecated; use Display") := by
  rfl

end leb128fmt_error_defaults
