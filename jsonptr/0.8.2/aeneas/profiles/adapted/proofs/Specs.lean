import JsonptrAdapted
import SpecModel

/-!
# Contracts for the adapted jsonptr bodies

Bridges from the generated Aeneas types to the specification model in
`SpecModel` (a verbatim port of the specification agent's draft), and the
total-success contract of each adapted target as a proposition. The
propositions are proved, if at all, in other modules; this module only states
them. A contract here is about the adapted function named in it, not about the
release API (see the profile's release-correspondence list).

Conventions: `bytes s` is the list of byte values of a generated slice.
Besides the representation invariants of the generated types, the premises are:
the Rust slice bound `len ≤ isize::MAX` (`SliceBound`), used exactly where the
specification allows it (targets 2, 3 and 7); the `Pointer` representation
premise of target 6 (`bytes xs = [] ∨ (bytes xs).head? = some 47`); in target 7,
that the pointer is the rendering of its decoded keys (`render keys = bytes ptr`);
and, in the single-step support statement, that the token is the encoding of
its decoded key (`encode k = bytes tok`).
-/

open Aeneas Aeneas.Std
open JsonptrSpecModel

namespace JsonptrAdaptedSpec

/-! ## Bridges -/

/-- Byte values of a generated slice. -/
def bytes (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

/-- Byte values of a generated vector. -/
def vbytes (v : alloc.vec.Vec U8) : List Nat := v.val.map (fun b => b.val)

/-- The Rust slice invariant `len ≤ isize::MAX`. -/
def SliceBound (s : Slice U8) : Prop := (s.length : Int) ≤ Isize.max

def encSource : jsonptr.token.InvalidEncoding → EncSource
  | .Tilde => .tilde
  | .Slash => .slash

def encError (e : jsonptr.token.EncodingError) : EncError :=
  ⟨e.offset.val, encSource e.source⟩

/-- Pointer outcome in the model; `none` for a value the model has no
counterpart for (an `InvalidEncoding` whose source is `Slash`, which the
contract therefore excludes). -/
def ptrOutcome : core.result.Result (Slice U8) jsonptr.pointer.ParseError → Option (Option PtrError)
  | .Ok _ => some none
  | .Err .NoLeadingSlash => some (some .noLeadingSlash)
  | .Err (.InvalidEncoding d ⟨t, .Tilde⟩) => some (some (.invalidEncoding d.val t.val))
  | .Err (.InvalidEncoding _ ⟨_, .Slash⟩) => none

def intKind : jsonptr.index.IntErrorKindAdapted → IntErrorKind
  | .Empty => .empty
  | .PosOverflow => .posOverflow

def indexError : jsonptr.index.ParseIndexErrorAdapted → IndexError
  | .InvalidInteger k => .invalidInteger (intKind k)
  | .LeadingZeros => .leadingZeros
  | .InvalidCharacter c => .invalidCharacter c.offset.val

def index : jsonptr.index.Index → Index
  | .Num n => .num n.val
  | .Next => .next

def indexOutcome : core.result.Result jsonptr.index.Index jsonptr.index.ParseIndexErrorAdapted →
    Res IndexError Index
  | .Ok i => .ok (index i)
  | .Err e => .error (indexError e)

open Aeneas.Data.ListN in
mutual
/-- Abstraction of the local document type to the specification tree. -/
def toTree : jsonptr.resolve.DocAdapted → Tree
  | .Leaf p => .leaf p.val
  | .Array ⟨⟨_, items, _⟩⟩ => .arr (toTrees items)
  | .Object ⟨⟨_, ms, _⟩⟩ => .obj (toMembers ms)
def toTrees {n : Nat} : ListN jsonptr.resolve.DocAdapted n → List Tree
  | .nil => []
  | .cons c cs => toTree c :: toTrees cs
def toMembers {n : Nat} :
    ListN (alloc.vec.Vec U8 × jsonptr.resolve.DocAdapted) n → List (List Nat × Tree)
  | .nil => []
  | .cons (k, c) cs => (vbytes k, toTree c) :: toMembers cs
end

def resolveError : jsonptr.resolve.ResolveErrorAdapted → ResolveError
  | .FailedToParseIndex p o e => .failedToParseIndex p.val o.val (indexError e)
  | .OutOfBounds p o e => .outOfBounds p.val o.val ⟨e.length.val, e.index.val⟩
  | .NotFound p o => .notFound p.val o.val
  | .Unreachable p o => .unreachable p.val o.val

def resolveOutcome :
    core.result.Result jsonptr.resolve.DocAdapted jsonptr.resolve.ResolveErrorAdapted →
    Res ResolveError Tree
  | .Ok d => .ok (toTree d)
  | .Err e => .error (resolveError e)

/-! ## Contracts (targets in the specification's priority order) -/

/-- Target 1, `pointer::validate`: on every byte slice the outcome is
`pointerError xs`, and success returns the unchanged input. -/
def ValidateContract : Prop :=
  ∀ xs : Slice U8, ∃ r, jsonptr.pointer.validate_adapted xs = .ok r ∧
    ptrOutcome r = some (pointerError (bytes xs)) ∧
    (∀ v, r = .Ok v → v = xs)

/-- Target 2, `Token::new` then `encoded`: the encoded bytes are `encode x`; the
input is reused (`none`) exactly when `needsNoEncoding x`. -/
def EncodeContract : Prop :=
  ∀ x : Slice U8, SliceBound x → ∃ r, jsonptr.token.new_adapted x = .ok r ∧
    match r with
    | none => needsNoEncoding (bytes x) = true ∧ encode (bytes x) = bytes x
    | some v => needsNoEncoding (bytes x) = false ∧ vbytes v = encode (bytes x)

/-- Target 3, `Token::decoded`: succeeds on every slice; on lawful input the
output is the unique `x` with `encode x = e`; the input is reused (`none`)
exactly when it contains no byte 126. -/
def DecodeContract : Prop :=
  ∀ e : Slice U8, SliceBound e → ∃ r, jsonptr.token.decoded_adapted e = .ok r ∧
    match r with
    | none => 126 ∉ bytes e ∧ ∀ x, encode x = bytes e → x = bytes e
    | some v => 126 ∈ bytes e ∧ ∀ x, encode x = bytes e → x = vbytes v

/-- Target 4, `Token::from_encoded`: the outcome is `firstEncError e`, and
success returns the unchanged input. -/
def FromEncodedContract : Prop :=
  ∀ e : Slice U8, ∃ r, jsonptr.token.from_encoded_adapted e = .ok r ∧
    match r with
    | .Ok v => v = e ∧ firstEncError (bytes e) = none
    | .Err err => firstEncError (bytes e) = some (encError err)

/-- Target 5, `Index::from_str` / `Token::to_index`: the outcome is
`parseIndex usize::MAX s`. -/
def IndexContract : Prop :=
  ∀ s : Slice U8, ∃ r, jsonptr.index.from_str_adapted s = .ok r ∧
    indexOutcome r = parseIndex Usize.max (bytes s)

/-- Target 6, `Pointer::split_front` (and so `tokens`): under the `Pointer`
representation invariant, nothing on empty input; otherwise the first token
and the remainder, with no byte lost and the token list preserved. -/
def SplitFrontContract : Prop :=
  ∀ xs : Slice U8, (bytes xs = [] ∨ (bytes xs).head? = some 47) →
    ∃ r, jsonptr.pointer.split_front_adapted xs = .ok r ∧
    match r with
    | none => bytes xs = []
    | some (tok, rem) =>
      bytes xs = 47 :: (bytes tok ++ bytes rem) ∧ 47 ∉ bytes tok ∧
      (bytes rem = [] ∨ (bytes rem).head? = some 47) ∧
      bytes tok :: encodedTokens (bytes rem) = encodedTokens (bytes xs)

/-- Support statement for target 7: one iteration of the release loop
(`resolve_step_adapted`), for an encoded token `tok` of the decoded key `k`,
agrees with the model's resolution of the single key `k` from the current node,
position and offset. The result node or error is exact. -/
def ResolveStepContract : Prop :=
  ∀ (value : jsonptr.resolve.DocAdapted) (tok : Slice U8) (position offset : Usize)
    (k : List Nat), encode k = bytes tok → SliceBound tok →
    ∃ r, jsonptr.resolve.resolve_step_adapted value tok position offset = .ok r ∧
      resolveOutcome r = resolveFrom Usize.max position.val offset.val (toTree value) [k]

/-- Target 7, JSON `Resolve::resolve` over the local document type, in the
approved tail-recursive form `resolve_recursive_adapted`: for a pointer that
renders the decoded keys `keys`, the outcome is `resolve usize::MAX root keys`,
with the exact node or error (position and offset included). -/
def ResolveContract : Prop :=
  ∀ (doc : jsonptr.resolve.DocAdapted) (ptr : Slice U8) (keys : List (List Nat)),
    render keys = bytes ptr → SliceBound ptr →
    ∃ r, jsonptr.resolve.resolve_recursive_adapted doc ptr = .ok r ∧
      resolveOutcome r = resolve Usize.max (toTree doc) keys

end JsonptrAdaptedSpec
