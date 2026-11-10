import Proofs.I8UncheckedPositive
open Aeneas Aeneas.Std
open lexical_parse_integer_parser_harness LexicalParseIntegerScalarSpec
namespace LexicalScalarProofs

def agreesSignedPartial (r : core.result.Result (I8 × Usize) lexical_util.error.Error) : SignedPartialResult → Prop
 | .value v i => match r with | .Ok (x,j) => x.val=v ∧ j.val=i | _ => False
 | .overflow i => match r with | .Err (.Overflow j) => j.val=i | _ => False
 | .underflow i => match r with | .Err (.Underflow j) => j.val=i | _ => False
 | .empty i => match r with | .Err (.Empty j) => j.val=i | _ => False
end LexicalScalarProofs
