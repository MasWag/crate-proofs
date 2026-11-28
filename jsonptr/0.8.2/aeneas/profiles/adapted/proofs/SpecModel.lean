/-!
# jsonptr 0.8.2 specification model (port for the adapted proofs package)

This module is a verbatim copy of the target 1–7 part of
`aeneas/profiles/adapted/spec-draft/SpecModel.lean` (SHA-256 `22891f76bd5959f5b1b45e529cf16b48889594691a178071ce02a4159499044e`),
written by the specification agent: every definition and closed test vector
from the start of `namespace JsonptrSpecModel` up to the section
"Specification sanity obligations", unchanged, plus the closed theorem
`resolve_root`. Omitted: the draft's module comment; its "specification sanity
obligation" theorems, which are left unproved in the draft and must not enter
the maintained proof tree; and the extension for specification sections 8–20,
which no phase-1 contract uses. Bytes are natural numbers; `Specs.lean`
bridges them to generated types.
-/

namespace JsonptrSpecModel

/-- Outcome of a Rust operation returning `Result<α, ε>`. (Core `Except` has
no decidable equality, which the closed test vectors need.) -/
inductive Res (ε α : Type) where
  | ok (value : α)
  | error (err : ε)
  deriving DecidableEq, Repr

/-! ## Bytes -/

/-- `'/'`, the RFC 6901 reference-token separator. -/
def SLASH : Nat := 47
/-- `'~'`, the RFC 6901 escape prefix. -/
def TILDE : Nat := 126
/-- `'0'`; `~0` denotes `~`. -/
def ZERO : Nat := 48
/-- `'1'`; `~1` denotes `/`. -/
def ONE : Nat := 49
/-- `'-'`; the whole token `-` denotes the position after the last array item. -/
def DASH : Nat := 45

/-! ## Token codec (RFC 6901 §3 and §4) -/

/-- Encoding of one decoded byte. -/
def encodeByte (b : Nat) : List Nat :=
  if b = 47 then [126, 49] else if b = 126 then [126, 48] else [b]

/-- The encoding `E` on UTF-8 byte lists. It agrees with the characterwise
encoding because `/` and `~` are ASCII and never occur inside a multibyte
sequence. -/
def encode : List Nat → List Nat
  | [] => []
  | b :: bs => encodeByte b ++ encode bs

/-- The decoding relation: `x` is a decoded spelling of the encoded bytes `e`. -/
def Decodes (e x : List Nat) : Prop := encode x = e

/-- The accepted language of `Token::from_encoded`: the image of `E`. -/
def ValidEncodedToken (e : List Nat) : Prop := ∃ x, encode x = e

/-- Executable decoder. `none` exactly outside the image of `E`. -/
def decode? : List Nat → Option (List Nat)
  | [] => some []
  | b :: rest =>
    if b = 47 then none
    else if b = 126 then
      match rest with
      | [] => none
      | c :: rest' =>
        if c = 48 then (decode? rest').map (fun x => 126 :: x)
        else if c = 49 then (decode? rest').map (fun x => 47 :: x)
        else none
    else (decode? rest).map (fun x => b :: x)

/-- Executable membership test for the image of `E`. -/
def validEncodedToken (e : List Nat) : Bool := (decode? e).isSome

/-- Which byte made an encoded token invalid. -/
inductive EncSource where
  | tilde
  | slash
  deriving DecidableEq, Repr

/-- Payload of `EncodingError`. -/
structure EncError where
  offset : Nat
  source : EncSource
  deriving DecidableEq, Repr

/-- First error of `Token::from_encoded`, scanning complete grammar atoms from
byte position `pos`.

* an unescaped slash reports `Slash` at the slash;
* a tilde at the end of input reports `Tilde` at the input length;
* a tilde followed by a slash reports `Slash` at that slash;
* a tilde followed by any other byte except `0`/`1` (including another tilde)
  reports `Tilde` at that following byte.

So a `Tilde` offset is one past the offending tilde, never the tilde itself. -/
def firstEncErrorFrom (pos : Nat) : List Nat → Option EncError
  | [] => none
  | b :: rest =>
    if b = 47 then some ⟨pos, .slash⟩
    else if b = 126 then
      match rest with
      | [] => some ⟨pos + 1, .tilde⟩
      | c :: rest' =>
        if c = 48 ∨ c = 49 then firstEncErrorFrom (pos + 2) rest'
        else if c = 47 then some ⟨pos + 1, .slash⟩
        else some ⟨pos + 1, .tilde⟩
    else firstEncErrorFrom (pos + 1) rest

/-- `Token::from_encoded(e)` is `Err` with exactly this payload, or `Ok` on `none`. -/
def firstEncError (e : List Nat) : Option EncError := firstEncErrorFrom 0 e

/-- `Token::new` returns its argument without re-allocating exactly when this holds. -/
def needsNoEncoding (x : List Nat) : Bool := x.all (fun b => b != 47 && b != 126)

/-! ## Pointer syntax (RFC 6901 §3) -/

/-- Rendering of a decoded key list: `"/" ++ E(key)` for each key.
`render [] = []` is the root pointer; `render [[]] = [47]` is one empty key. -/
def render : List (List Nat) → List Nat
  | [] => []
  | k :: ks => 47 :: (encode k ++ render ks)

/-- Rendering of already encoded tokens. -/
def renderEncoded : List (List Nat) → List Nat
  | [] => []
  | t :: ts => 47 :: (t ++ renderEncoded ts)

/-- Split at every slash; always returns at least one piece. -/
def splitSlash : List Nat → List (List Nat)
  | [] => [[]]
  | b :: rest =>
    if b = 47 then [] :: splitSlash rest
    else
      match splitSlash rest with
      | [] => [[b]]
      | p :: ps => (b :: p) :: ps

/-- The encoded tokens of a pointer string, as `Pointer::tokens` yields them:
split at slashes and discard the piece before the first slash. -/
def encodedTokens (xs : List Nat) : List (List Nat) := (splitSlash xs).drop 1

/-- Payload of the pointer `ParseError`. -/
inductive PtrError where
  | noLeadingSlash
  /-- `ptrOffset` is the byte position of the separator opening the offending
  token; `srcOffset` is the offending tilde's position minus `ptrOffset`. -/
  | invalidEncoding (ptrOffset srcOffset : Nat)
  deriving DecidableEq, Repr

/-- A tilde at `j` not followed by ASCII `0` or `1` (same notion as the default
profile's `BadEscape`). -/
def BadEscape (xs : List Nat) (j : Nat) : Prop :=
  xs[j]? = some 126 ∧ xs[j + 1]? ≠ some 48 ∧ xs[j + 1]? ≠ some 49

/-- Declarative accepted language of the pointer parser, including the empty input. -/
def ValidPointer (xs : List Nat) : Prop :=
  (xs = [] ∨ xs[0]? = some 47) ∧ ∀ j, ¬ BadEscape xs j

/-- Declarative first-error contract of the public validation wrapper. Unlike
the default profile's `ValidationPost`, the domain includes the empty input. -/
def PointerPost (xs : List Nat) : Option PtrError → Prop
  | none => ValidPointer xs
  | some .noLeadingSlash => xs ≠ [] ∧ xs[0]? ≠ some 47
  | some (.invalidEncoding d t) =>
    let j := d + t
    xs[0]? = some 47 ∧ BadEscape xs j ∧ (∀ k, k < j → ¬ BadEscape xs k) ∧
      xs[d]? = some 47 ∧ d < j ∧ (∀ k, d < k → k < j → xs[k]? ≠ some 47)

/-- Executable scan behind `pointerError`: `pos` is the current byte position
and `sep` the position of the most recent separator. -/
def ptrScan (pos sep : Nat) : List Nat → Option PtrError
  | [] => none
  | b :: rest =>
    if b = 47 then ptrScan (pos + 1) pos rest
    else if b = 126 then
      match rest with
      | [] => some (.invalidEncoding sep (pos - sep))
      | c :: rest' =>
        if c = 48 ∨ c = 49 then ptrScan (pos + 2) sep rest'
        else some (.invalidEncoding sep (pos - sep))
    else ptrScan (pos + 1) sep rest

/-- Executable first error of pointer validation on every byte list. -/
def pointerError (xs : List Nat) : Option PtrError :=
  match xs with
  | [] => none
  | b :: _ => if b = 47 then ptrScan 0 0 xs else some .noLeadingSlash

/-! ## Array index grammar (RFC 6901 §4) -/

/-- The two `IntErrorKind`s reachable from `Index::from_str`. -/
inductive IntErrorKind where
  | empty
  | posOverflow
  deriving DecidableEq, Repr

/-- Payload of `ParseIndexError`. -/
inductive IndexError where
  | leadingZeros
  /-- Offset counts characters; see `firstNonDigit`. -/
  | invalidCharacter (offset : Nat)
  | invalidInteger (kind : IntErrorKind)
  deriving DecidableEq, Repr

/-- `Index`. -/
inductive Index where
  | num (n : Nat)
  | next
  deriving DecidableEq, Repr

def isDigit (b : Nat) : Bool := decide (48 ≤ b) && decide (b ≤ 57)

/-- Position of the first byte that is not an ASCII digit. Every earlier byte
is ASCII, so on UTF-8 input this byte position equals the character position
that the release computes with `chars().position`. -/
def firstNonDigitFrom (pos : Nat) : List Nat → Option Nat
  | [] => none
  | b :: rest => if isDigit b then firstNonDigitFrom (pos + 1) rest else some pos

def firstNonDigit (s : List Nat) : Option Nat := firstNonDigitFrom 0 s

/-- Unbounded decimal value of a list of ASCII digits, most significant first. -/
def decimalValue (s : List Nat) : Nat := s.foldl (fun acc d => 10 * acc + (d - 48)) 0

/-- `Index::from_str` on the UTF-8 bytes of its argument. `usizeMax` is the
target's `usize::MAX` (2^64 − 1 on the extraction target).

Precedence: `"-"`; then `LeadingZeros` for every spelling longer than `"0"`
that starts with `0` (even when a later byte is not a digit); then
`InvalidCharacter` at the first non-digit; then `Empty`; then `PosOverflow`. -/
def parseIndex (usizeMax : Nat) (s : List Nat) : Res IndexError Index :=
  if s = [45] then .ok .next
  else if s.head? = some 48 ∧ s ≠ [48] then .error .leadingZeros
  else
    match firstNonDigit s with
    | some off => .error (.invalidCharacter off)
    | none =>
      if s = [] then .error (.invalidInteger .empty)
      else if decimalValue s ≤ usizeMax then .ok (.num (decimalValue s))
      else .error (.invalidInteger .posOverflow)

/-- RFC 6901 §4 `array-index = %x30 / ( %x31-39 *(%x30-39) )`, as a predicate. -/
def IsArrayIndexSpelling (s : List Nat) : Prop :=
  s = [48] ∨ (∃ d ds, s = d :: ds ∧ 49 ≤ d ∧ d ≤ 57 ∧ ∀ b, b ∈ ds → isDigit b = true)

/-- Payload of `OutOfBoundsError`. -/
structure OutOfBounds where
  length : Nat
  index : Nat
  deriving DecidableEq, Repr

/-- `Index::for_len` (strict bound), restated from the default profile. -/
def forLen (i : Index) (length : Nat) : Res OutOfBounds Nat :=
  let n := match i with
    | .num n => n
    | .next => length
  if n < length then .ok n else .error ⟨length, n⟩

/-! ## Resolution over a finite tree (RFC 6901 §4)

`Tree` is a specification object. It says nothing about `serde_json::Value`;
see the specification for what stays open. -/

/-- A finite document. Object members are an association list in which the
first entry for a key wins; a document with unique keys never observes that
choice. Leaves carry an opaque payload. -/
inductive Tree where
  | leaf (payload : Nat)
  | arr (items : List Tree)
  | obj (members : List (List Nat × Tree))

/-- Exact-key lookup on decoded UTF-8 bytes; no normalisation. -/
def lookupKey (k : List Nat) : List (List Nat × Tree) → Option Tree
  | [] => none
  | (k', v) :: rest => if k' = k then some v else lookupKey k rest

/-- Payload of `resolve::Error`. -/
inductive ResolveError where
  | failedToParseIndex (position offset : Nat) (source : IndexError)
  | outOfBounds (position offset : Nat) (source : OutOfBounds)
  | notFound (position offset : Nat)
  | unreachable (position offset : Nat)
  deriving DecidableEq, Repr

/-- Resolution of the remaining decoded keys from a node. `position` counts
consumed tokens and `offset` is the byte position, in the rendered pointer, of
the separator that opens the current token.

On an array the release parses the *encoded* token as an index; on an object
it looks up the *decoded* key. -/
def resolveFrom (usizeMax : Nat) (position offset : Nat) (t : Tree) :
    List (List Nat) → Res ResolveError Tree
  | [] => .ok t
  | k :: ks =>
    let next := offset + 1 + (encode k).length
    match t with
    | .arr items =>
      match parseIndex usizeMax (encode k) with
      | .error e => .error (.failedToParseIndex position offset e)
      | .ok i =>
        match forLen i items.length with
        | .error e => .error (.outOfBounds position offset e)
        | .ok n =>
          match items[n]? with
          | some child => resolveFrom usizeMax (position + 1) next child ks
          | none => .error (.outOfBounds position offset ⟨items.length, n⟩)
    | .obj members =>
      match lookupKey k members with
      | some child => resolveFrom usizeMax (position + 1) next child ks
      | none => .error (.notFound position offset)
    | .leaf _ => .error (.unreachable position offset)

/-- `Resolve::resolve` for the pointer rendering `keys`. -/
def resolve (usizeMax : Nat) (root : Tree) (keys : List (List Nat)) :
    Res ResolveError Tree :=
  resolveFrom usizeMax 0 0 root keys

/-! ## Closed test vectors

Each agrees with the native release (Rust 1.91.0, `aarch64-apple-darwin`). -/

theorem tv_encode : encode [97, 47, 98, 126, 99] = [97, 126, 49, 98, 126, 48, 99] := by decide
/-- `E("~1") = "~01"`, and it decodes back to `"~1"`, not to `"/"`. -/
theorem tv_encode_escape_lookalike : encode [126, 49] = [126, 48, 49] := by decide
theorem tv_decode_escape_lookalike : decode? [126, 48, 49] = some [126, 49] := by decide
theorem tv_decode_invalid : decode? [97, 126, 98] = none := by decide

/-- `"a~b"`: `Tilde` at 2, the byte after the tilde. -/
theorem tv_enc_tilde_mid : firstEncError [97, 126, 98] = some ⟨2, .tilde⟩ := by decide
/-- `"a~"`: `Tilde` at the length. -/
theorem tv_enc_tilde_end : firstEncError [97, 126] = some ⟨2, .tilde⟩ := by decide
/-- `"~~"`: `Tilde` at the second tilde. -/
theorem tv_enc_tilde_tilde : firstEncError [126, 126] = some ⟨1, .tilde⟩ := by decide
/-- `"~/"`: `Slash` at 1, not `Tilde`. -/
theorem tv_enc_tilde_slash : firstEncError [126, 47] = some ⟨1, .slash⟩ := by decide
/-- `"~01/"`: `Slash` at 3. -/
theorem tv_enc_slash_after_escape : firstEncError [126, 48, 49, 47] = some ⟨3, .slash⟩ := by decide
theorem tv_enc_ok : firstEncError [126, 48, 126, 49] = none := by decide

theorem tv_ptr_root : pointerError [] = none := by decide
theorem tv_ptr_empty_keys : pointerError [47, 47] = none := by decide
/-- `"~"`: the missing slash takes precedence over the bad escape. -/
theorem tv_ptr_no_slash : pointerError [126] = some .noLeadingSlash := by decide
/-- `"/x/a~"`. -/
theorem tv_ptr_tilde_end : pointerError [47, 120, 47, 97, 126] = some (.invalidEncoding 2 2) := by decide
/-- `"/~~"`. -/
theorem tv_ptr_tilde_tilde : pointerError [47, 126, 126] = some (.invalidEncoding 0 1) := by decide
theorem tv_tokens_root : encodedTokens [] = [] := by decide
theorem tv_tokens_empty_keys : encodedTokens [47, 47] = [[], []] := by decide
theorem tv_render_empty_key : render [[]] = [47] := by decide

theorem tv_idx_next : parseIndex 255 [45] = .ok .next := by decide
theorem tv_idx_zero : parseIndex 255 [48] = .ok (.num 0) := by decide
/-- `"00"`. -/
theorem tv_idx_leading : parseIndex 255 [48, 48] = .error .leadingZeros := by decide
/-- `"0a"`: `LeadingZeros` precedes `InvalidCharacter`. -/
theorem tv_idx_leading_nondigit : parseIndex 255 [48, 97] = .error .leadingZeros := by decide
/-- `"+1"`. -/
theorem tv_idx_plus : parseIndex 255 [43, 49] = .error (.invalidCharacter 0) := by decide
/-- `"-1"` is not `Next`. -/
theorem tv_idx_minus_one : parseIndex 255 [45, 49] = .error (.invalidCharacter 0) := by decide
/-- `"1é"` (bytes 49, 195, 169). -/
theorem tv_idx_multibyte : parseIndex 255 [49, 195, 169] = .error (.invalidCharacter 1) := by decide
theorem tv_idx_empty : parseIndex 255 [] = .error (.invalidInteger .empty) := by decide
/-- With an 8-bit bound, `"255"` fits and `"256"` overflows. -/
theorem tv_idx_max : parseIndex 255 [50, 53, 53] = .ok (.num 255) := by decide
theorem tv_idx_overflow : parseIndex 255 [50, 53, 54] = .error (.invalidInteger .posOverflow) := by decide

/-- `{"a": [x, y]}` at `/a/1` selects `y`. -/
theorem tv_resolve_ok :
    resolve 255 (.obj [([97], .arr [.leaf 7, .leaf 8])]) [[97], [49]] = .ok (.leaf 8) := by rfl
/-- The same document with tokens `a` then `-`: `OutOfBounds` at position 1, offset 2, with
index = length = 2. -/
theorem tv_resolve_next :
    resolve 255 (.obj [([97], .arr [.leaf 7, .leaf 8])]) [[97], [45]] =
      .error (.outOfBounds 1 2 ⟨2, 2⟩) := by rfl
/-- At `/a/01`: `FailedToParseIndex` with `LeadingZeros`. -/
theorem tv_resolve_leading :
    resolve 255 (.obj [([97], .arr [.leaf 7, .leaf 8])]) [[97], [48, 49]] =
      .error (.failedToParseIndex 1 2 .leadingZeros) := by rfl
/-- At `/a/0/x`: `Unreachable` at position 2, offset 4. -/
theorem tv_resolve_unreachable :
    resolve 255 (.obj [([97], .arr [.leaf 7, .leaf 8])]) [[97], [48], [120]] =
      .error (.unreachable 2 4) := by rfl
/-- At `/~1` (key `"/"`): `NotFound` at position 0, offset 0. -/
theorem tv_resolve_not_found :
    resolve 255 (.obj [([97], .arr [.leaf 7, .leaf 8])]) [[47]] = .error (.notFound 0 0) := by rfl

/-- The empty pointer selects the root (closed). -/
theorem resolve_root (usizeMax : Nat) (root : Tree) : resolve usizeMax root [] = .ok root := by
  rfl

end JsonptrSpecModel
