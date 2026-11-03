import OptionExtAdapted

open Aeneas Aeneas.Std
namespace OptionExtAdaptedContracts

abbrev mapOrElse := @option_ext_adapted.core.option.Option.Insts.Option_ext_adaptedOptionExt.map_or_else2

/-- Mathematical lazy option elimination, independent of the translated body. -/
def mapLazyDefault {T U : Type} (mapping : T → U) (defaultValue : U)
    (self : Option T) : U :=
  match self with
  | none => defaultValue
  | some x => mapping x

theorem map_or_else2_none {T U F D : Type}
    (fInst : core.ops.function.FnOnce F T U)
    (dInst : core.ops.function.FnOnce D Unit U) (f : F) (d : D) :
    mapOrElse fInst dInst none f d = dInst.call_once d () := rfl

theorem map_or_else2_some {T U F D : Type}
    (fInst : core.ops.function.FnOnce F T U)
    (dInst : core.ops.function.FnOnce D Unit U) (f : F) (d : D) (x : T) :
    mapOrElse fInst dInst (some x) f d = fInst.call_once f x := rfl

/-- Total success requires only the selected callback to satisfy its postcondition. -/
theorem map_or_else2_postcondition {T U F D : Type}
    (fInst : core.ops.function.FnOnce F T U)
    (dInst : core.ops.function.FnOnce D Unit U)
    (self : Option T) (f : F) (d : D) (post : U → Prop)
    (selected : match self with
      | none => ∃ u, dInst.call_once d () = .ok u ∧ post u
      | some x => ∃ u, fInst.call_once f x = .ok u ∧ post u) :
    ∃ u, mapOrElse fInst dInst self f d = .ok u ∧ post u := by
  cases self with
  | none => exact selected
  | some x => exact selected

/-- The unused callback is unrestricted, including failure or divergence. -/
theorem map_or_else2_correct {T U F D : Type}
    (fInst : core.ops.function.FnOnce F T U)
    (dInst : core.ops.function.FnOnce D Unit U)
    (self : Option T) (f : F) (d : D) (mapping : T → U) (defaultValue : U)
    (selected : match self with
      | none => dInst.call_once d () = .ok defaultValue
      | some x => fInst.call_once f x = .ok (mapping x)) :
    ∃ u, mapOrElse fInst dInst self f d = .ok u ∧
      u = mapLazyDefault mapping defaultValue self := by
  cases self with
  | none => exact ⟨defaultValue, selected, rfl⟩
  | some x => exact ⟨mapping x, selected, rfl⟩

end OptionExtAdaptedContracts
