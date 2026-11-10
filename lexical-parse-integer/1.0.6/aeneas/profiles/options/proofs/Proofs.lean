import Options
import OptionsSpecs

open Aeneas Aeneas.Std Result lexical_parse_integer
namespace LexicalParseIntegerOptionsProofs
open LexicalParseIntegerOptionsSpec

theorem builder_new :
    options.OptionsBuilder.new = .ok { no_multi_digit := defaultState } := by rfl

theorem builder_get (b : options.OptionsBuilder) :
    options.OptionsBuilder.get_no_multi_digit b = .ok (get b.no_multi_digit) := by rfl

theorem builder_set (b : options.OptionsBuilder) (flag : Bool) :
    options.OptionsBuilder.impl.no_multi_digit b flag =
      .ok { no_multi_digit := set b.no_multi_digit flag } := by rfl

theorem builder_valid (b : options.OptionsBuilder) :
    options.OptionsBuilder.is_valid b = .ok (valid b.no_multi_digit) := by rfl

theorem builder_build_unchecked (b : options.OptionsBuilder) :
    options.OptionsBuilder.build_unchecked b =
      .ok { no_multi_digit := buildState b.no_multi_digit } := by rfl

theorem builder_build (b : options.OptionsBuilder) :
    options.OptionsBuilder.build b =
      .ok (.Ok { no_multi_digit := buildState b.no_multi_digit }) := by simp [options.OptionsBuilder.build, options.OptionsBuilder.build_unchecked, buildState]

theorem builder_default :
    options.OptionsBuilder.Insts.CoreDefaultDefault.default =
      .ok { no_multi_digit := defaultState } := by rfl

theorem options_builder :
    options.Options.builder = .ok { no_multi_digit := defaultState } := by rfl

theorem options_new :
    options.Options.new = .ok { no_multi_digit := defaultState } := by simp [options.Options.new, options.Options.builder, options.OptionsBuilder.new, options.OptionsBuilder.build_unchecked, defaultState]

theorem options_from_radix (radix : Std.U8) :
    options.Options.from_radix radix =
      .ok { no_multi_digit := fromRadix radix.val } := by simp [options.Options.from_radix, options.Options.new, options.Options.builder, options.OptionsBuilder.new, options.OptionsBuilder.build_unchecked, fromRadix, defaultState]

theorem options_rebuild (o : options.Options) :
    options.Options.rebuild o =
      .ok { no_multi_digit := rebuild o.no_multi_digit } := by rfl

theorem options_valid (o : options.Options) :
    options.Options.is_valid o = .ok (valid o.no_multi_digit) := by simp [options.Options.is_valid, options.Options.rebuild, options.OptionsBuilder.is_valid, valid]

theorem options_get (o : options.Options) :
    options.Options.get_no_multi_digit o = .ok (get o.no_multi_digit) := by rfl

theorem options_no_multi_digit (o : options.Options) (flag : Bool) :
    options.Options.impl.no_multi_digit o flag =
      .ok { no_multi_digit := set o.no_multi_digit flag } := by rfl

theorem options_set_no_multi_digit (o : options.Options) (flag : Bool) :
    options.Options.set_no_multi_digit o flag =
      .ok { no_multi_digit := set o.no_multi_digit flag } := by rfl

theorem options_default :
    options.Options.Insts.CoreDefaultDefault.default =
      .ok { no_multi_digit := defaultState } := by simp [options.Options.Insts.CoreDefaultDefault.default, options.Options.new, options.Options.builder, options.OptionsBuilder.new, options.OptionsBuilder.build_unchecked, defaultState]

theorem parse_options_valid (o : options.Options) :
    options.Options.Insts.Lexical_utilOptionsParseOptions.is_valid o =
      .ok (valid o.no_multi_digit) := by simp [options.Options.Insts.Lexical_utilOptionsParseOptions.is_valid, options.Options.is_valid, options.Options.rebuild, options.OptionsBuilder.is_valid, valid]

theorem standard_state :
    options.STANDARD = .ok { no_multi_digit := standard } := by
  simp [options.STANDARD, options.Options.new, options.Options.builder,
    options.OptionsBuilder.new, options.OptionsBuilder.build_unchecked,
    standard, defaultState]

end LexicalParseIntegerOptionsProofs
