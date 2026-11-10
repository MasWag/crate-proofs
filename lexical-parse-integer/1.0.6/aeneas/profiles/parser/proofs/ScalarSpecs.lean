import Init

/-! Independent mathematical scan semantics. Normal parse errors are values of
this model, not failure of the Aeneas execution relation. -/
namespace LexicalParseIntegerScalarSpec

inductive ScanResult where
  | value (magnitude : Nat)
  | invalidDigit (index : Nat)
  | overflow (index : Nat)
  | underflow (index : Nat)
  deriving DecidableEq, Repr

def decimalDigit (byte : Nat) : Option Nat :=
  if 48 ≤ byte ∧ byte < 58 then some (byte - 48) else none

/-- The first nondigit or first excessive prefix ends the scan. The index is
the original index of that byte, before any iterator advancement. Empty input
returns the entry magnitude; sign/empty-input policy belongs to the caller. -/
def boundedScan (bound : Nat) (negative : Bool) :
    List Nat → Nat → Nat → ScanResult
  | [], magnitude, _ => .value magnitude
  | byte :: rest, magnitude, index =>
    match decimalDigit byte with
    | none => .invalidDigit index
    | some digit =>
      let next := 10 * magnitude + digit
      if next ≤ bound then boundedScan bound negative rest next (index + 1)
      else if negative then .underflow index else .overflow index

def checkedU32Scan (bytes : List Nat) (initial index : Nat) : ScanResult :=
  boundedScan (2^32 - 1) false bytes initial index

/-- Signed scans represent the absolute magnitude. Their implementation
contracts must separately require a nonnegative/ nonpositive entry accumulator
and relate a successful signed output to plus/minus this magnitude. -/
def checkedI32PositiveScan (bytes : List Nat) (initial index : Nat) : ScanResult :=
  boundedScan (2^31 - 1) false bytes initial index

def checkedI32NegativeScan (bytes : List Nat) (initial index : Nat) : ScanResult :=
  boundedScan (2^31) true bytes initial index

/-- Complete-parser front-end errors are separate from scanning an empty suffix:
the latter legitimately returns its entry magnitude. -/
inductive CompleteResult where
  | empty (index : Nat)
  | scanned (result : ScanResult)
  deriving DecidableEq, Repr

/-- Standard decimal unsigned-byte syntax: one optional leading plus, at least
one remaining byte, and the first-event bounded decimal scan. A minus is an
invalid byte, not an unsigned sign. Indices count original input bytes.
This specification does not mention the implementation's two-byte optimization.
Specification authored by Astra; source-adapter equivalence is a separate claim. -/
def completeU8 (bytes : List Nat) : CompleteResult :=
  let (digits, index) :=
    match bytes with
    | 43 :: rest => (rest, 1)
    | _ => (bytes, 0)
  match digits with
  | [] => .empty index
  | _ :: _ => .scanned (boundedScan 255 false digits 0 index)

/-- Partial unsigned parsing exposes both the value and the absolute count of
consumed bytes. Empty input is a front-end error, not a scan termination error. -/
inductive PartialResult where
  | value (magnitude consumed : Nat)
  | empty (index : Nat)
  | overflow (index : Nat)
  deriving DecidableEq, Repr

/-- Independent bounded decimal partial scan. A nondigit is not consumed and
ends the scan successfully, even if no digits have been read. Overflow on a
digit ends the scan immediately, before any later nondigit can be considered.
The entry magnitude must be in range in contracts for private scan helpers. -/
def partialScan (bound : Nat) : List Nat → Nat → Nat → PartialResult
  | [], magnitude, index => .value magnitude index
  | byte :: rest, magnitude, index =>
    match decimalDigit byte with
    | none => .value magnitude index
    | some digit =>
      let next := 10 * magnitude + digit
      if next ≤ bound then partialScan bound rest next (index + 1)
      else .overflow index

/-- Standard decimal unsigned-byte partial syntax, independently specified by
Astra. One optional initial plus counts toward the consumed prefix. Empty or
sign-only input is Empty at the post-sign index; any other initial nondigit,
including minus or a second plus, gives zero with that index as consumed count.
No optimization boundary or implementation iterator state appears in this model. -/
def partialU8 (bytes : List Nat) : PartialResult :=
  let (digits, index) :=
    match bytes with
    | 43 :: rest => (rest, 1)
    | _ => (bytes, 0)
  match digits with
  | [] => .empty index
  | _ :: _ => partialScan 255 digits 0 index

/-- The independently specified signed result converts a magnitude to an
integer only at the observable boundary, preserving the asymmetric minimum. -/
def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(Int.ofNat magnitude) else Int.ofNat magnitude

inductive SignedCompleteResult where
  | value (value : Int)
  | empty (index : Nat)
  | invalidDigit (index : Nat)
  | overflow (index : Nat)
  | underflow (index : Nat)
  deriving DecidableEq, Repr

def signedCompleteResult (negative : Bool) : ScanResult → SignedCompleteResult
  | .value magnitude => .value (signedValue negative magnitude)
  | .invalidDigit i => .invalidDigit i
  | .overflow i => .overflow i
  | .underflow i => .underflow i

/-- Exactly one optional ASCII sign; both signs count toward all original
indices. Sign-only input is empty, and a second sign is a nondigit. -/
def signedInput (bytes : List Nat) : List Nat × Nat × Bool :=
  match bytes with
  | 43 :: rest => (rest, 1, false)
  | 45 :: rest => (rest, 1, true)
  | _ => (bytes, 0, false)

/-- Standard decimal signed-byte complete semantics, authored by Astra.
The negative path admits magnitude 128, the nonnegative path at most 127. -/
def completeI8 (bytes : List Nat) : SignedCompleteResult :=
  let (digits, index, negative) := signedInput bytes
  match digits with
  | [] => .empty index
  | _ :: _ => signedCompleteResult negative
      (boundedScan (if negative then 128 else 127) negative digits 0 index)

inductive SignedPartialResult where
  | value (value : Int) (consumed : Nat)
  | empty (index : Nat)
  | overflow (index : Nat)
  | underflow (index : Nat)
  deriving DecidableEq, Repr

/-- Signed partial scanning excludes the terminating nondigit from the count.
Overflow/underflow is decided on each digit before examining later bytes. -/
def signedPartialScan (bound : Nat) (negative : Bool) :
    List Nat → Nat → Nat → SignedPartialResult
  | [], magnitude, index => .value (signedValue negative magnitude) index
  | byte :: rest, magnitude, index =>
    match decimalDigit byte with
    | none => .value (signedValue negative magnitude) index
    | some digit =>
      let next := 10 * magnitude + digit
      if next ≤ bound then signedPartialScan bound negative rest next (index + 1)
      else if negative then .underflow index else .overflow index

/-- Nonempty post-sign nondigit input returns zero and the post-sign count,
including after a minus. Empty and sign-only input remain Empty errors. -/
def partialI8 (bytes : List Nat) : SignedPartialResult :=
  let (digits, index, negative) := signedInput bytes
  match digits with
  | [] => .empty index
  | _ :: _ => signedPartialScan (if negative then 128 else 127) negative digits 0 index

/-- Sign parsing alone does not enforce nonempty post-sign digits. -/
inductive SignResult where
  | accepted (negative : Bool) (cursor : Nat)
  | invalidPositiveSign (index : Nat)
  | missingSign (index : Nat)
  deriving DecidableEq, Repr

/-- Independent sign-helper contract for a byte at the current cursor.
A forbidden plus has priority over a required-sign error. An unsigned minus
is not accepted as a sign; with a required sign it therefore gives MissingSign.
An absent byte likewise gives MissingSign exactly when a sign is required.
Contracts for machine cursors must separately discharge representability of
the one-step advance on an accepted sign. Authored by Astra. -/
def parseSign (byte : Option Nat) (cursor : Nat)
    (signed noPositive required : Bool) : SignResult :=
  match byte with
  | some 43 => if noPositive then .invalidPositiveSign cursor
               else .accepted false (cursor + 1)
  | some 45 => if signed then .accepted true (cursor + 1)
               else if required then .missingSign cursor else .accepted false cursor
  | _ => if required then .missingSign cursor else .accepted false cursor

end LexicalParseIntegerScalarSpec
