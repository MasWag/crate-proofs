import Observer

open Aeneas Aeneas.Std

namespace leb128fmt_error_observers

theorem source_is_none_spec (error : leb128fmt.Error) :
    source_is_none error = .ok true := by
  rfl

theorem cause_is_none_spec (error : leb128fmt.Error) :
    cause_is_none error = .ok true := by
  rfl

end leb128fmt_error_observers
