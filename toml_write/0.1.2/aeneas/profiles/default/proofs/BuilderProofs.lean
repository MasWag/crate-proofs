import TomlWrite.Funs

open Aeneas Aeneas.Std
open toml_write.string

namespace TomlWriteVerification

private def stringResult (builder : TomlStringBuilder) (encoding : Encoding) :
    TomlString :=
  ⟨builder.decoded, encoding, builder.metrics.newline⟩

private def keyResult (builder : TomlKeyBuilder) (encoding : Option Encoding) :
    TomlKey :=
  ⟨builder.decoded, encoding⟩

private theorem noQuotes (n : U8) : (¬ (0#u8 < n)) ↔ n.val = 0 := by
  change (¬ (0 < n.val)) ↔ n.val = 0
  omega

private theorem fewQuotes (n : U8) : (¬ (2#u8 < n)) ↔ n.val ≤ 2 := by
  change (¬ (2 < n.val)) ↔ n.val ≤ 2
  omega

theorem string_basic (builder : TomlStringBuilder) :
    builder.as_basic = .ok (stringResult builder .BasicString) := rfl

theorem string_ml_basic (builder : TomlStringBuilder) :
    builder.as_ml_basic = .ok (stringResult builder .MlBasicString) := rfl

theorem string_literal (builder : TomlStringBuilder) :
    builder.as_literal = .ok (if builder.metrics.escape_codes = false ∧
      builder.metrics.max_seq_single_quotes.val = 0 ∧ builder.metrics.newline = false
      then some (stringResult builder .LiteralString) else none) := by
  unfold TomlStringBuilder.as_literal stringResult
  simp only [← noQuotes]
  repeat' split
  all_goals simp_all

theorem string_ml_literal (builder : TomlStringBuilder) :
    builder.as_ml_literal = .ok (if builder.metrics.escape_codes = false ∧
      builder.metrics.max_seq_single_quotes.val ≤ 2
      then some (stringResult builder .MlLiteralString) else none) := by
  unfold TomlStringBuilder.as_ml_literal stringResult
  simp only [← fewQuotes]
  repeat' split
  all_goals simp_all

theorem string_basic_pretty (builder : TomlStringBuilder) :
    builder.as_basic_pretty = .ok (if builder.metrics.escape_codes = false ∧
      builder.metrics.escape = false ∧ builder.metrics.max_seq_double_quotes.val = 0 ∧
      builder.metrics.newline = false
      then some (stringResult builder .BasicString) else none) := by
  unfold TomlStringBuilder.as_basic_pretty TomlStringBuilder.as_basic stringResult
  simp only [← noQuotes]
  repeat' split
  all_goals simp_all

theorem string_ml_basic_pretty (builder : TomlStringBuilder) :
    builder.as_ml_basic_pretty = .ok (if builder.metrics.escape_codes = false ∧
      builder.metrics.escape = false ∧ builder.metrics.max_seq_double_quotes.val ≤ 2
      then some (stringResult builder .MlBasicString) else none) := by
  unfold TomlStringBuilder.as_ml_basic_pretty TomlStringBuilder.as_ml_basic stringResult
  simp only [← fewQuotes]
  repeat' split
  all_goals simp_all

theorem key_basic (builder : TomlKeyBuilder) :
    builder.as_basic = .ok (keyResult builder (some .BasicString)) := rfl

theorem key_unquoted (builder : TomlKeyBuilder) :
    builder.as_unquoted = .ok (if builder.metrics.unquoted
      then some (keyResult builder none) else none) := by
  unfold TomlKeyBuilder.as_unquoted keyResult
  split <;> simp_all

theorem key_literal (builder : TomlKeyBuilder) :
    builder.as_literal = .ok (if builder.metrics.escape_codes = false ∧
      builder.metrics.single_quotes = false
      then some (keyResult builder (some .LiteralString)) else none) := by
  unfold TomlKeyBuilder.as_literal keyResult
  repeat' split
  all_goals simp_all

theorem key_basic_pretty (builder : TomlKeyBuilder) :
    builder.as_basic_pretty = .ok (if builder.metrics.escape_codes = false ∧
      builder.metrics.escape = false ∧ builder.metrics.double_quotes = false
      then some (keyResult builder (some .BasicString)) else none) := by
  unfold TomlKeyBuilder.as_basic_pretty TomlKeyBuilder.as_basic keyResult
  cases builder.metrics.escape_codes <;> cases builder.metrics.escape <;>
    cases builder.metrics.double_quotes <;> simp_all

end TomlWriteVerification
