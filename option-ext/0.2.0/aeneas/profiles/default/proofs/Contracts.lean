import OptionExt

open Aeneas Aeneas.Std

namespace OptionExtContracts

/-- Independent Boolean membership, with the comparison direction candidate to element. -/
def member {T U : Type _} (compare : U → T → Bool) (opt : Option T) (x : U) : Bool :=
  match opt with
  | none => false
  | some t => compare x t

/-- Independent mathematical option elimination. -/
def mapDefault {T V : Type _} (mapping : T → V) (default : V) (opt : Option T) : V :=
  match opt with
  | none => default
  | some t => mapping t

abbrev contains := @option_ext.core.option.Option.Insts.Option_extOptionExt.contains
abbrev map_or2 := @option_ext.core.option.Option.Insts.Option_extOptionExt.map_or2

theorem contains_none {T U : Type _} (eqInst : core.cmp.PartialEq U T) (x : U) :
    contains eqInst none x = Result.ok false := rfl

/-- Exact equality includes propagation of any comparison failure. -/
theorem contains_some {T U : Type _} (eqInst : core.cmp.PartialEq U T) (t : T) (x : U) :
    contains eqInst (some t) x = eqInst.eq x t := rfl

/-- Total success requires refinement only of the selected comparison. -/
theorem contains_correct {T U : Type _} (eqInst : core.cmp.PartialEq U T)
    (compare : U → T → Bool) (opt : Option T) (x : U)
    (selected : ∀ t, opt = some t → eqInst.eq x t = Result.ok (compare x t)) :
    ∃ out, contains eqInst opt x = Result.ok out ∧ out = member compare opt x := by
  cases opt with
  | none => exact ⟨false, rfl, rfl⟩
  | some t => exact ⟨compare x t, selected t rfl, rfl⟩

/-- No laws of equality are imposed on the heterogeneous relation. -/
theorem contains_relation_correct {T U : Type _} (eqInst : core.cmp.PartialEq U T)
    (relation : U → T → Prop) (opt : Option T) (x : U)
    (selected : ∀ t, opt = some t →
      ∃ b, eqInst.eq x t = Result.ok b ∧ (b = true ↔ relation x t)) :
    ∃ out, contains eqInst opt x = Result.ok out ∧
      (out = true ↔ match opt with | none => False | some t => relation x t) := by
  cases opt with
  | none => exact ⟨false, rfl, by simp⟩
  | some t =>
      obtain ⟨b, success, reflection⟩ := selected t rfl
      exact ⟨b, success, reflection⟩

theorem map_or2_none {T V F : Type _} (call : core.ops.function.FnOnce F T V)
    (f : F) (default : V) :
    map_or2 call (none : Option T) f default = Result.ok default := rfl

/-- Exact equality includes propagation of any selected callback failure. -/
theorem map_or2_some {T V F : Type _} (call : core.ops.function.FnOnce F T V)
    (t : T) (f : F) (default : V) :
    map_or2 call (some t) f default = call.call_once f t := rfl

/-- The none branch imposes no callback-success premise. -/
theorem map_or2_correct {T V F : Type _} (call : core.ops.function.FnOnce F T V)
    (mapping : T → V) (opt : Option T) (f : F) (default : V)
    (selected : ∀ t, opt = some t → call.call_once f t = Result.ok (mapping t)) :
    ∃ out, map_or2 call opt f default = Result.ok out ∧
      out = mapDefault mapping default opt := by
  cases opt with
  | none => exact ⟨default, rfl, rfl⟩
  | some t => exact ⟨mapping t, selected t rfl, rfl⟩

theorem map_or2_some_postcondition {T V F : Type _} (call : core.ops.function.FnOnce F T V)
    (t : T) (f : F) (default out : V) (property : T → V → Prop)
    (success : call.call_once f t = Result.ok out) (holds : property t out) :
    ∃ result, map_or2 call (some t) f default = Result.ok result ∧ property t result :=
  ⟨out, success, holds⟩

end OptionExtContracts
