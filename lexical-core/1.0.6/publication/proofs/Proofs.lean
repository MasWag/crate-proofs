import Facade
open Aeneas Aeneas.Std
namespace LexicalCorePublicationProofs
open lexical_core

/-- Generic complete parsing forwards every success and error unchanged. -/
theorem parse_eq {N : Type} (inst : FromLexical N) (bytes : Slice U8) :
  parse inst bytes = inst.from_lexical bytes := rfl

theorem parse_partial_eq {N : Type} (inst : FromLexical N) (bytes : Slice U8) :
  parse_partial inst bytes = inst.from_lexical_partial bytes := rfl

theorem parse_with_options_eq {N O : Type} (fmt : U128)
    (inst : FromLexicalWithOptions N O) (bytes : Slice U8) (opts : O) :
  parse_with_options fmt inst bytes opts = inst.from_lexical_with_options fmt bytes opts := rfl

theorem parse_partial_with_options_eq {N O : Type} (fmt : U128)
    (inst : FromLexicalWithOptions N O) (bytes : Slice U8) (opts : O) :
  parse_partial_with_options fmt inst bytes opts =
    inst.from_lexical_partial_with_options fmt bytes opts := rfl

/-- Equality includes both the returned slice and the mutable-borrow backward function. -/
theorem write_eq {N : Type} (inst : ToLexical N) (value : N) (bytes : Slice U8) :
  write inst value bytes = inst.to_lexical value bytes := rfl

theorem write_with_options_eq {N O : Type} (fmt : U128)
    (inst : ToLexicalWithOptions N O) (value : N) (bytes : Slice U8) (opts : O) :
  write_with_options fmt inst value bytes opts =
    inst.to_lexical_with_options fmt value bytes opts := rfl

/-- The facade preserves any independent output relation, conditional on an actual
    successful dictionary call. This premise is not a proof of that dictionary. -/
theorem parse_spec {N : Type} (inst : FromLexical N) (bytes : Slice U8)
    (P : core.result.Result N lexical_util.error.Error → Prop)
    (h : ∃ out, inst.from_lexical bytes = Result.ok out ∧ P out) :
    ∃ out, parse inst bytes = Result.ok out ∧ P out := h

theorem parse_partial_spec {N : Type} (inst : FromLexical N) (bytes : Slice U8)
    (P : core.result.Result (N × Usize) lexical_util.error.Error → Prop)
    (h : ∃ out, inst.from_lexical_partial bytes = Result.ok out ∧ P out) :
    ∃ out, parse_partial inst bytes = Result.ok out ∧ P out := h

theorem parse_with_options_spec {N O : Type} (fmt : U128)
    (inst : FromLexicalWithOptions N O) (bytes : Slice U8) (opts : O)
    (P : core.result.Result N lexical_util.error.Error → Prop)
    (h : ∃ out, inst.from_lexical_with_options fmt bytes opts = Result.ok out ∧ P out) :
    ∃ out, parse_with_options fmt inst bytes opts = Result.ok out ∧ P out := h

theorem parse_partial_with_options_spec {N O : Type} (fmt : U128)
    (inst : FromLexicalWithOptions N O) (bytes : Slice U8) (opts : O)
    (P : core.result.Result (N × Usize) lexical_util.error.Error → Prop)
    (h : ∃ out, inst.from_lexical_partial_with_options fmt bytes opts = Result.ok out ∧ P out) :
    ∃ out, parse_partial_with_options fmt inst bytes opts = Result.ok out ∧ P out := h

theorem write_spec {N : Type} (inst : ToLexical N) (value : N) (bytes : Slice U8)
    (P : Slice U8 × (Slice U8 → Slice U8) → Prop)
    (h : ∃ out, inst.to_lexical value bytes = Result.ok out ∧ P out) :
    ∃ out, write inst value bytes = Result.ok out ∧ P out := h

theorem write_with_options_spec {N O : Type} (fmt : U128)
    (inst : ToLexicalWithOptions N O) (value : N) (bytes : Slice U8) (opts : O)
    (P : Slice U8 × (Slice U8 → Slice U8) → Prop)
    (h : ∃ out, inst.to_lexical_with_options fmt value bytes opts = Result.ok out ∧ P out) :
    ∃ out, write_with_options fmt inst value bytes opts = Result.ok out ∧ P out := h
end LexicalCorePublicationProofs
