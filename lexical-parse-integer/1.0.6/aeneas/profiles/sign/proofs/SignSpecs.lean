import Init

namespace LexicalParseIntegerSignSpec

/-- Sign parsing alone does not enforce nonempty post-sign digits. -/
inductive SignResult where
  | accepted (negative : Bool) (cursor : Nat)
  | invalidPositiveSign (index : Nat)
  | missingSign (index : Nat)
  deriving DecidableEq, Repr

/-- Independent byte and flag contract, copied verbatim from the independently
authored parser ScalarSpecs.parseSign model. The caller supplies flags and a
representable cursor. -/
def parseSign (byte : Option Nat) (cursor : Nat)
    (signed noPositive required : Bool) : SignResult :=
  match byte with
  | some 43 => if noPositive then .invalidPositiveSign cursor
               else .accepted false (cursor + 1)
  | some 45 => if signed then .accepted true (cursor + 1)
               else if required then .missingSign cursor else .accepted false cursor
  | _ => if required then .missingSign cursor else .accepted false cursor

end LexicalParseIntegerSignSpec
