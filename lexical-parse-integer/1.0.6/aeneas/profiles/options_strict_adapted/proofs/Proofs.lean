import Strict
import OptionsSpecs

open Aeneas Aeneas.Std Result
namespace LexicalStrictAdaptedProofs
open lexical_parse_integer_options_strict_adapted LexicalParseIntegerOptionsSpec

/-- Total success of the adapted body for both builder states. -/
theorem strict_success (b : options.OptionsBuilder) :
    options.OptionsBuilder.build_strict b =
      .ok { no_multi_digit := buildState b.no_multi_digit } := by
  simp [options.OptionsBuilder.build_strict, options.OptionsBuilder.build,
    options.OptionsBuilder.build_unchecked, buildState]

theorem small_numbers :
    options.SMALL_NUMBERS = .ok { no_multi_digit := smallNumbers } := by
  unfold options.SMALL_NUMBERS
  simp [options.Options.builder, options.OptionsBuilder.new,
    options.OptionsBuilder.impl.no_multi_digit, strict_success, buildState,
    smallNumbers]

theorem large_numbers :
    options.LARGE_NUMBERS = .ok { no_multi_digit := largeNumbers } := by
  unfold options.LARGE_NUMBERS
  simp [options.Options.builder, options.OptionsBuilder.new,
    options.OptionsBuilder.impl.no_multi_digit, strict_success, buildState,
    largeNumbers]

end LexicalStrictAdaptedProofs
