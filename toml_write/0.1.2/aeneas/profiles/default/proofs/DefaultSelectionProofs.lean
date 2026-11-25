import TomlDefaultModel.TomlWrite
import MetricsProofs
import ValueMetricsProofs

open Aeneas Aeneas.Std Result
open TomlDefault.string

namespace TomlWriteVerification.DefaultSelection

private def keyPretty (m : KeyMetrics) : Prop :=
  m.escape_codes = false ∧ m.escape = false ∧ m.double_quotes = false

private def keyLiteral (m : KeyMetrics) : Prop :=
  m.escape_codes = false ∧ m.single_quotes = false

structure StringObservations where
  singleQuotes : Nat
  doubleQuotes : Nat
  controls : Bool
  backslash : Bool
  newline : Bool

def observeStringMetrics (m : ValueMetrics) : StringObservations :=
  ⟨m.max_seq_single_quotes.val, m.max_seq_double_quotes.val, m.escape_codes, m.escape, m.newline⟩

private theorem observeStringNewline (m : ValueMetrics) :
    (observeStringMetrics m).newline = m.newline := rfl

private def stringPretty (m : StringObservations) : Prop :=
  m.controls = false ∧ m.backslash = false ∧ m.doubleQuotes = 0 ∧
    m.newline = false

private def stringLiteral (m : StringObservations) : Prop :=
  m.controls = false ∧ m.singleQuotes = 0 ∧ m.newline = false

private def stringMlPretty (m : StringObservations) : Prop :=
  m.controls = false ∧ m.backslash = false ∧ m.doubleQuotes ≤ 2

private def stringMlLiteral (m : StringObservations) : Prop :=
  m.controls = false ∧ m.singleQuotes ≤ 2

instance (m : KeyMetrics) : Decidable (keyPretty m) := inferInstanceAs (Decidable (_ ∧ _))
instance (m : KeyMetrics) : Decidable (keyLiteral m) := inferInstanceAs (Decidable (_ ∧ _))
instance (m : StringObservations) : Decidable (stringPretty m) := inferInstanceAs (Decidable (_ ∧ _))
instance (m : StringObservations) : Decidable (stringLiteral m) := inferInstanceAs (Decidable (_ ∧ _))
instance (m : StringObservations) : Decidable (stringMlPretty m) := inferInstanceAs (Decidable (_ ∧ _))
instance (m : StringObservations) : Decidable (stringMlLiteral m) := inferInstanceAs (Decidable (_ ∧ _))

def defaultKeyEncoding (m : KeyMetrics) : Option DefaultEncoding :=
  if m.unquoted then none
  else if keyPretty m then some .BasicString
  else if keyLiteral m then some .LiteralString
  else some .BasicString

def defaultStringEncoding (m : StringObservations) : DefaultEncoding :=
  if stringPretty m then .BasicString
  else if stringLiteral m then .LiteralString
  else if stringMlPretty m then .MlBasicString
  else if stringMlLiteral m then .MlLiteralString
  else if m.newline then .MlBasicString
  else .BasicString

private def keyResult (b : TomlKeyBuilder) (encoding : Option DefaultEncoding) : TomlKey :=
  ⟨b.decoded, encoding⟩

private def stringResult (b : TomlStringBuilder) (encoding : DefaultEncoding) : TomlString :=
  ⟨b.decoded, encoding, b.metrics.newline⟩

private theorem noQuotes (n : U8) : (¬ (0#u8 < n)) ↔ n.val = 0 := by
  change (¬ (0 < n.val)) ↔ n.val = 0
  omega

private theorem fewQuotes (n : U8) : (¬ (2#u8 < n)) ↔ n.val ≤ 2 := by
  change (¬ (2 < n.val)) ↔ n.val ≤ 2
  omega

private theorem keyUnquoted (b : TomlKeyBuilder) :
    b.as_unquoted = .ok (if b.metrics.unquoted then some (keyResult b none) else none) := by
  cases h : b.metrics.unquoted <;> simp_all [TomlKeyBuilder.as_unquoted, keyResult]

private theorem keyBasicPretty (b : TomlKeyBuilder) :
    b.as_basic_pretty = .ok (if keyPretty b.metrics
      then some (keyResult b (some .BasicString)) else none) := by
  cases h₁ : b.metrics.escape_codes <;> cases h₂ : b.metrics.escape <;>
    cases h₃ : b.metrics.double_quotes <;>
    simp_all [TomlKeyBuilder.as_basic_pretty, TomlKeyBuilder.as_basic, keyPretty, keyResult]

private theorem keyAsLiteral (b : TomlKeyBuilder) :
    b.as_literal = .ok (if keyLiteral b.metrics
      then some (keyResult b (some .LiteralString)) else none) := by
  cases h₁ : b.metrics.escape_codes <;> cases h₂ : b.metrics.single_quotes <;>
    simp_all [TomlKeyBuilder.as_literal, keyLiteral, keyResult]

private theorem stringBasicPretty (b : TomlStringBuilder) :
    b.as_basic_pretty = .ok (if stringPretty (observeStringMetrics b.metrics)
      then some (stringResult b .BasicString) else none) := by
  unfold TomlStringBuilder.as_basic_pretty TomlStringBuilder.as_basic stringResult stringPretty observeStringMetrics
  simp only [← noQuotes]
  repeat' split
  all_goals simp_all

private theorem stringAsLiteral (b : TomlStringBuilder) :
    b.as_literal = .ok (if stringLiteral (observeStringMetrics b.metrics)
      then some (stringResult b .LiteralString) else none) := by
  unfold TomlStringBuilder.as_literal stringResult stringLiteral observeStringMetrics
  simp only [← noQuotes]
  repeat' split
  all_goals simp_all

private theorem stringMlBasicPretty (b : TomlStringBuilder) :
    b.as_ml_basic_pretty = .ok (if stringMlPretty (observeStringMetrics b.metrics)
      then some (stringResult b .MlBasicString) else none) := by
  unfold TomlStringBuilder.as_ml_basic_pretty TomlStringBuilder.as_ml_basic
    stringResult stringMlPretty observeStringMetrics
  simp only [← fewQuotes]
  repeat' split
  all_goals simp_all

private theorem stringAsMlLiteral (b : TomlStringBuilder) :
    b.as_ml_literal = .ok (if stringMlLiteral (observeStringMetrics b.metrics)
      then some (stringResult b .MlLiteralString) else none) := by
  unfold TomlStringBuilder.as_ml_literal stringResult stringMlLiteral observeStringMetrics
  simp only [← fewQuotes]
  repeat' split
  all_goals simp_all

theorem key_default (b : TomlKeyBuilder) :
    b.as_default = .ok ⟨b.decoded, defaultKeyEncoding b.metrics⟩ := by
  simp only [TomlKeyBuilder.as_default, keyUnquoted, keyBasicPretty, keyAsLiteral,
    TomlKeyBuilder.as_basic, defaultKeyEncoding, bind_ok]
  by_cases hu : b.metrics.unquoted = true
  · simp [hu, keyResult]
  by_cases hp : keyPretty b.metrics
  · simp [hu, hp, keyResult]
  by_cases hl : keyLiteral b.metrics <;> simp [hu, hp, hl, keyResult]

theorem string_default (b : TomlStringBuilder) :
    b.as_default = .ok ⟨b.decoded, defaultStringEncoding (observeStringMetrics b.metrics), b.metrics.newline⟩ := by
  simp only [TomlStringBuilder.as_default, stringBasicPretty, stringAsLiteral, stringMlBasicPretty,
    stringAsMlLiteral, TomlStringBuilder.as_basic, TomlStringBuilder.as_ml_basic,
    defaultStringEncoding, bind_ok]
  by_cases hp : stringPretty (observeStringMetrics b.metrics)
  · simp [hp, stringResult]
  by_cases hl : stringLiteral (observeStringMetrics b.metrics)
  · simp [hp, hl, stringResult]
  by_cases hm : stringMlPretty (observeStringMetrics b.metrics)
  · simp [hp, hl, hm, stringResult]
  by_cases hml : stringMlLiteral (observeStringMetrics b.metrics)
  · simp [hp, hl, hm, hml, stringResult]
  cases h : b.metrics.newline <;> simp [hp, hl, hm, hml, observeStringNewline, h]

-- These equations model the release's lazy Option combinators at the functional
-- level. The Rust callback bodies themselves are outside generated Lean.
private def unwrapOrElse (selected : Option α) (fallback : Unit → α) : α :=
  match selected with
  | some value => value
  | none => fallback ()

theorem key_option_chain (b : TomlKeyBuilder) :
    let unquoted := if b.metrics.unquoted then some (keyResult b none) else none
    let pretty (_ : Unit) := if keyPretty b.metrics
      then some (keyResult b (some .BasicString)) else none
    let literal (_ : Unit) := if keyLiteral b.metrics
      then some (keyResult b (some .LiteralString)) else none
    unwrapOrElse ((unquoted.orElse pretty).orElse literal)
      (fun () => keyResult b (some .BasicString)) =
      ⟨b.decoded, defaultKeyEncoding b.metrics⟩ := by
  dsimp only
  by_cases hu : b.metrics.unquoted = true
  · simp [hu, keyResult, defaultKeyEncoding, Option.orElse, unwrapOrElse]
  by_cases hp : keyPretty b.metrics
  · simp [hu, hp, keyResult, defaultKeyEncoding, Option.orElse, unwrapOrElse]
  by_cases hl : keyLiteral b.metrics <;>
    simp [hu, hp, hl, keyResult, defaultKeyEncoding, Option.orElse, unwrapOrElse]

theorem string_option_chain (b : TomlStringBuilder) :
    let pretty := if stringPretty (observeStringMetrics b.metrics)
      then some (stringResult b .BasicString) else none
    let literal (_ : Unit) := if stringLiteral (observeStringMetrics b.metrics)
      then some (stringResult b .LiteralString) else none
    let mlPretty (_ : Unit) := if stringMlPretty (observeStringMetrics b.metrics)
      then some (stringResult b .MlBasicString) else none
    let mlLiteral (_ : Unit) := if stringMlLiteral (observeStringMetrics b.metrics)
      then some (stringResult b .MlLiteralString) else none
    let fallback := if b.metrics.newline then .MlBasicString else .BasicString
    unwrapOrElse (((pretty.orElse literal).orElse mlPretty).orElse mlLiteral)
      (fun () => stringResult b fallback) =
      ⟨b.decoded, defaultStringEncoding (observeStringMetrics b.metrics), b.metrics.newline⟩ := by
  dsimp only
  by_cases hp : stringPretty (observeStringMetrics b.metrics)
  · simp [hp, stringResult, defaultStringEncoding, Option.orElse, unwrapOrElse]
  by_cases hl : stringLiteral (observeStringMetrics b.metrics)
  · simp [hp, hl, stringResult, defaultStringEncoding, Option.orElse, unwrapOrElse]
  by_cases hm : stringMlPretty (observeStringMetrics b.metrics)
  · simp [hp, hl, hm, stringResult, defaultStringEncoding, Option.orElse, unwrapOrElse]
  by_cases hml : stringMlLiteral (observeStringMetrics b.metrics) <;>
    simp [hp, hl, hm, hml, stringResult, defaultStringEncoding, observeStringNewline,
      Option.orElse, unwrapOrElse]
  rfl

-- The two translations generate separate Lean types. These adapters preserve
-- every field of the original extracted builder passed to adapted selection.
def adaptKeyBuilder (b : toml_write.string.TomlKeyBuilder) : TomlKeyBuilder :=
  ⟨b.decoded, ⟨b.metrics.unquoted, b.metrics.single_quotes, b.metrics.double_quotes,
    b.metrics.escape_codes, b.metrics.escape⟩⟩

def adaptStringBuilder (b : toml_write.string.TomlStringBuilder) : TomlStringBuilder :=
  ⟨b.decoded, ⟨b.metrics.max_seq_single_quotes, b.metrics.max_seq_double_quotes,
    b.metrics.escape_codes, b.metrics.escape, b.metrics.newline⟩⟩

theorem key_default_after_new (text : Str) :
    (do
      let b ← toml_write.string.TomlKeyBuilder.new text
      (adaptKeyBuilder b).as_default) =
      .ok ⟨text, defaultKeyEncoding (adaptKeyBuilder ⟨text, keyMetricsSpec text⟩).metrics⟩ := by
  simp [key_constructor, key_default, adaptKeyBuilder]

private def stringObservationsOf (metrics : Nat × Nat × Bool × Bool × Bool) :
    StringObservations :=
  let (single, double, controls, backslash, newline) := metrics
  ⟨single, double, controls, backslash, newline⟩

theorem string_default_after_new (text : Str)
    (singleFits : longestQuoteRun 39#u8 text.val ≤ 255)
    (doubleFits : longestQuoteRun 34#u8 text.val ≤ 255) :
    let observations := stringObservationsOf (valueMetricsSpec text.val)
    (do
      let b ← toml_write.string.TomlStringBuilder.new text
      (adaptStringBuilder b).as_default) =
      .ok ⟨text, defaultStringEncoding observations, observations.newline⟩ := by
  obtain ⟨metrics, hnew, hmetrics⟩ := string_constructor text singleFits doubleFits
  have hobs := congrArg stringObservationsOf hmetrics
  change observeStringMetrics (adaptStringBuilder ⟨text, metrics⟩).metrics =
    stringObservationsOf (valueMetricsSpec text.val) at hobs
  dsimp only
  rw [← hobs, hnew]
  simp [string_default, adaptStringBuilder, observeStringMetrics]

end TomlWriteVerification.DefaultSelection
