import Utf8SourceAccessor

open Aeneas Aeneas.Std Result

namespace Utf8SourceAccessorProofs

/-- The direct Rust trait-call wrapper dispatches to the release type's inherited
    standard-library default, extracted with its actual body. -/
theorem decode_error_source_total (error : utf8_source_accessor.utf8.DecodeError) :
    ∃ out, utf8_source_accessor.decode_error_source error = .ok out ∧ out = none := by
  exact ⟨none, rfl, rfl⟩

end Utf8SourceAccessorProofs
