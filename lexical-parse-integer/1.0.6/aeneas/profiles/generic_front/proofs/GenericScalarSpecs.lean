import DigitSpecs

/-! Independent generic scalar semantics, authored by Astra.

The intended Rust theorem domain is radix 2..36 and a positive integer width
(8, 16, 32, 64, 128, or the selected platform width). Definitions are total on
Nat, but totalization outside this domain is not a Rust API claim. Bytes range
over all U8 values; no valid-digit or successful-parse premise is appropriate
for a complete/partial front-end contract. This module does not change the
previously maintained decimal specifications.
-/
namespace LexicalParseIntegerGenericSpec

def unsignedBound (width : Nat) : Nat := 2^width - 1
def positiveBound (width : Nat) : Nat := 2^(width - 1) - 1
def negativeBound (width : Nat) : Nat := 2^(width - 1)

def magnitudeBound (width : Nat) (signed negative : Bool) : Nat :=
  if signed then (if negative then negativeBound width else positiveBound width)
  else unsignedBound width

def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

inductive ScanResult where
  | value (magnitude consumed : Nat)
  | invalidDigit (index : Nat)
  | overflow (index : Nat)
  | underflow (index : Nat)
  deriving DecidableEq, Repr

/-- First-event semantics over unbounded magnitudes. A nondigit is examined
before any arithmetic: complete mode rejects it, partial mode stops without
consuming it. Overflow on a digit precedes any later event. Empty remaining
input returns the entry magnitude and original absolute cursor. Private scan
contracts require the entry magnitude to lie within bound; negative signed
machine accumulators must additionally equal minus that magnitude. -/
def scan (radix bound : Nat) (negative isPartial : Bool) :
    List Nat → Nat → Nat → ScanResult
  | [], magnitude, index => .value magnitude index
  | byte :: rest, magnitude, index =>
    match LexicalParseIntegerDigitSpec.digit radix byte with
    | none => if isPartial then .value magnitude index else .invalidDigit index
    | some digit =>
      let next := radix * magnitude + digit
      if next ≤ bound then scan radix bound negative isPartial rest next (index + 1)
      else if negative then .underflow index else .overflow index

/-- Standard syntax accepts one optional plus and, for signed targets only,
one optional minus. An unsigned minus is an ordinary nondigit. -/
def inputAfterSign (signed : Bool) (bytes : List Nat) : List Nat × Nat × Bool :=
  match bytes with
  | 43 :: rest => (rest, 1, false)
  | 45 :: rest => if signed then (rest, 1, true) else (bytes, 0, false)
  | _ => (bytes, 0, false)

inductive CompleteResult where
  | value (value : Int)
  | empty (index : Nat)
  | invalidDigit (index : Nat)
  | overflow (index : Nat)
  | underflow (index : Nat)
  deriving DecidableEq, Repr

def completeResult (negative : Bool) : ScanResult → CompleteResult
  | .value magnitude _ => .value (signedValue negative magnitude)
  | .invalidDigit i => .invalidDigit i
  | .overflow i => .overflow i
  | .underflow i => .underflow i

def parseComplete (width : Nat) (signed : Bool) (radix : Nat)
    (bytes : List Nat) : CompleteResult :=
  let (digits, index, negative) := inputAfterSign signed bytes
  match digits with
  | [] => .empty index
  | _ :: _ => completeResult negative
      (scan radix (magnitudeBound width signed negative) negative false digits 0 index)

inductive PartialResult where
  | value (value : Int) (consumed : Nat)
  | empty (index : Nat)
  | invalidDigit (index : Nat)
  | overflow (index : Nat)
  | underflow (index : Nat)
  deriving DecidableEq, Repr

/-- The invalidDigit constructor makes this projection total on ScanResult;
scan with partial=true never produces it. No caller may assume successful
parsing: empty/sign-only and excessive prefixes retain their exact errors. -/
def partialResult (negative : Bool) : ScanResult → PartialResult
  | .value magnitude index => .value (signedValue negative magnitude) index
  | .invalidDigit i => .invalidDigit i
  | .overflow i => .overflow i
  | .underflow i => .underflow i

def parsePartial (width : Nat) (signed : Bool) (radix : Nat)
    (bytes : List Nat) : PartialResult :=
  let (digits, index, negative) := inputAfterSign signed bytes
  match digits with
  | [] => .empty index
  | _ :: _ => partialResult negative
      (scan radix (magnitudeBound width signed negative) negative true digits 0 index)

/-- Number of initial digits selected by the release scalar optimization.
This is a separate implementation-selection observable, not part of the
mathematical parser definition. byteWidth is positive and width=8*byteWidth
in corresponding Rust obligations. -/
def overflowDigits (byteWidth : Nat) (signed : Bool) (radix : Nat) : Nat :=
  if radix ≤ 16 then 2 * byteWidth - (if signed then 1 else 0) else byteWidth

/-- Sufficient mathematical range condition for a private unchecked region
of at most count digits, for radix≥2. It bounds every valid prefix; invalid
bytes terminate before participating in multiplication or addition. -/
def uncheckedBound (radix bound initial count : Nat) : Prop :=
  radix^count * initial + (radix^count - 1) ≤ bound

/-- Obligation for the selected zero-entry optimization. Implementations must
prove this proposition for their selected type/radix, then prove wrapping
arithmetic equals the mathematical fold. A predicate is not itself a proof.
For signed targets the positive bound is conservative for either sign. -/
def selectedPrefixSafe (byteWidth : Nat) (signed : Bool) (radix : Nat) : Prop :=
  uncheckedBound radix (magnitudeBound (8 * byteWidth) signed false) 0
    (overflowDigits byteWidth signed radix)

/- A no_multi_digit=true adapter must preserve the release's unchecked-prefix
selection and subsequent checked scan, including an immediate partial return
if a nondigit occurs inside the prefix. Whole-input contracts are complete and
partial above, with no prefix-length restriction on callers. Machine-cursor
representability, source adaptation, and release equivalence remain separate
obligations. Proving this selected option does not prove option independence.
-/

end LexicalParseIntegerGenericSpec
