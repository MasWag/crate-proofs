/-!
# jsonptr 0.8.2 — independent specification model (draft)

Written by the specification agent before any adapted source or generated Lean
existed. It imports nothing: bytes are natural numbers (intended range 0–255,
but no definition relies on that bound) and strings are their UTF-8 byte lists.

The implementation agent instantiates these definitions against the generated
types (`U8`/`Usize` values via `.val`, slices and vectors via their lists) and
proves total-success theorems about the generated bodies.

Every `sorry` in this file is a **specification sanity obligation**: a property
of the model itself, stated so that a wrong model is detected. None of them may
be used, imported, or left open in the maintained proof tree. The `tv_*`
theorems are closed test vectors; each was also observed on the native release.
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

/-! ## Specification sanity obligations

Model-internal facts. Proving them is optional for the adapted profile, but a
proof must not live in the maintained tree with `sorry`. -/

/-- SANITY OBLIGATION. Decoding inverts encoding (RFC 6901 §4 round trip). -/
theorem decode_encode (x : List Nat) : decode? (encode x) = some x := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The decoder is sound, so decoded spellings are unique. -/
theorem encode_of_decode (e x : List Nat) (h : decode? e = some x) : encode x = e := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `E` is injective. -/
theorem encode_injective (x y : List Nat) (h : encode x = encode y) : x = y := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The executable test decides the image of `E`. -/
theorem validEncodedToken_iff (e : List Nat) :
    validEncodedToken e = true ↔ ValidEncodedToken e := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `from_encoded` succeeds exactly on the image of `E`. -/
theorem firstEncError_none_iff (e : List Nat) :
    firstEncError e = none ↔ ValidEncodedToken e := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Error offsets stay inside the input, and reach its
length only for a final pending tilde. -/
theorem firstEncError_offset_le (e : List Nat) (err : EncError)
    (h : firstEncError e = some err) :
    err.offset ≤ e.length ∧ (err.offset = e.length → err.source = .tilde) := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. A `Slash` error names a slash; a `Tilde` error names the
position just after a tilde that is not followed by `0` or `1`. -/
theorem firstEncError_points_at (e : List Nat) (err : EncError)
    (h : firstEncError e = some err) :
    (err.source = .slash → e[err.offset]? = some 47) ∧
    (err.source = .tilde → 0 < err.offset ∧ e[err.offset - 1]? = some 126 ∧
      e[err.offset]? ≠ some 48 ∧ e[err.offset]? ≠ some 49 ∧ e[err.offset]? ≠ some 47) := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. An encoded spelling needs no change exactly when the
decoded one has no slash or tilde. -/
theorem encode_eq_self_iff (x : List Nat) : encode x = x ↔ needsNoEncoding x = true := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Encoding at most doubles the length (capacity bound). -/
theorem encode_length (x : List Nat) :
    x.length ≤ (encode x).length ∧ (encode x).length ≤ 2 * x.length := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The executable pointer scan meets the declarative contract. -/
theorem pointerError_post (xs : List Nat) : PointerPost xs (pointerError xs) := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The declarative contract determines the result. -/
theorem PointerPost_unique (xs : List Nat) (r r' : Option PtrError)
    (h : PointerPost xs r) (h' : PointerPost xs r') : r = r' := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. A string parses exactly when it renders some key list. -/
theorem pointerError_none_iff (xs : List Nat) :
    pointerError xs = none ↔ ∃ keys, render keys = xs := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The tokens of a rendered pointer are the encoded keys,
so root and one empty key stay distinct. -/
theorem encodedTokens_render (keys : List (List Nat)) :
    encodedTokens (render keys) = keys.map encode := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Splitting loses no byte of a slash-led string. -/
theorem renderEncoded_encodedTokens (xs : List Nat) (h : xs = [] ∨ xs[0]? = some 47) :
    renderEncoded (encodedTokens xs) = xs := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The pointer error and the token error agree: the token
opened by the reported separator fails `from_encoded` with the same offset. -/
theorem pointerError_token_agrees (xs : List Nat) (d t : Nat)
    (h : pointerError xs = some (.invalidEncoding d t)) :
    ∃ tok, (splitSlash (xs.drop (d + 1))).head? = some tok ∧
      firstEncError tok = some ⟨t, .tilde⟩ := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The parser accepts `-` and exactly the RFC 6901
`array-index` spellings whose value fits the machine word. -/
theorem parseIndex_ok_iff (usizeMax : Nat) (s : List Nat) (n : Nat) :
    parseIndex usizeMax s = .ok (.num n) ↔
      IsArrayIndexSpelling s ∧ decimalValue s = n ∧ n ≤ usizeMax := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `Next` has the single spelling `-`. -/
theorem parseIndex_next_iff (usizeMax : Nat) (s : List Nat) :
    parseIndex usizeMax s = .ok .next ↔ s = [45] := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Parsing the encoded token (what the release does) and
parsing the decoded key give the same result, error payloads included. -/
theorem parseIndex_encode (usizeMax : Nat) (k : List Nat) :
    parseIndex usizeMax (encode k) = parseIndex usizeMax k := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `resolveFrom`'s defensive `items[n]?` failure branch is
unreachable: a strict bound always selects an item. -/
theorem forLen_ok_lt (i : Index) (length n : Nat) (h : forLen i length = .ok n) :
    n < length := by
  sorry -- spec sanity obligation, draft only

/-- The empty pointer selects the root (closed). -/
theorem resolve_root (usizeMax : Nat) (root : Tree) : resolve usizeMax root [] = .ok root := by
  rfl

/-- SANITY OBLIGATION. Error positions and offsets name a token of the pointer:
`position` is below the token count and `offset` is the rendered length of the
keys before it. -/
theorem resolve_error_location (usizeMax : Nat) (root : Tree) (keys : List (List Nat))
    (err : ResolveError) (h : resolve usizeMax root keys = .error err) :
    ∃ position offset,
      (err = .notFound position offset ∨ err = .unreachable position offset ∨
        (∃ e, err = .failedToParseIndex position offset e) ∨
        (∃ e, err = .outOfBounds position offset e)) ∧
      position < keys.length ∧ offset = (render (keys.take position)).length := by
  sorry -- spec sanity obligation, draft only

/-! # Extension: the remaining public API (specification sections 8–20)

Added after targets 1–7. Nothing above this line changed. Pointers are byte
lists satisfying `ValidPointer`; `encodedTokens` gives their token lists. The
definitions below state each operation on token lists (or on bytes where the
operation is a byte operation) so that the intended result is independent of
the release's string manipulation. -/

/-! ## Pointer navigation (§8) -/

/-- `Pointer::count`. -/
def count (xs : List Nat) : Nat := (encodedTokens xs).length

/-- `Pointer::front` / `first`. -/
def front (xs : List Nat) : Option (List Nat) := (encodedTokens xs).head?

/-- `Pointer::back` / `last`. -/
def back (xs : List Nat) : Option (List Nat) := (encodedTokens xs).getLast?

/-- `Pointer::split_front`: first token and the remaining pointer. -/
def splitFront (xs : List Nat) : Option (List Nat × List Nat) :=
  match encodedTokens xs with
  | [] => none
  | t :: ts => some (t, renderEncoded ts)

/-- `Pointer::split_back`: the parent pointer and the last token. -/
def splitBack (xs : List Nat) : Option (List Nat × List Nat) :=
  match (encodedTokens xs).getLast? with
  | none => none
  | some t => some (renderEncoded (encodedTokens xs).dropLast, t)

/-- `Pointer::parent`. -/
def parent (xs : List Nat) : Option (List Nat) := (splitBack xs).map (fun p => p.1)

/-- `Pointer::get(usize)`. -/
def getToken (xs : List Nat) (i : Nat) : Option (List Nat) := (encodedTokens xs)[i]?

/-- `Pointer::split_at_offset`: a byte split, allowed exactly at a slash. -/
def splitAtOffset (xs : List Nat) (offset : Nat) : Option (List Nat × List Nat) :=
  if xs[offset]? = some 47 then some (xs.take offset, xs.drop offset) else none

/-- A component of a pointer. -/
inductive Component where
  | root
  | token (encoded : List Nat)
  deriving DecidableEq, Repr

/-- `Pointer::components`: `Root` first, then every token. -/
def components (xs : List Nat) : List Component :=
  .root :: (encodedTokens xs).map .token

/-- One end of a `(Bound<usize>, Bound<usize>)` index. -/
inductive Bound where
  | included (n : Nat)
  | excluded (n : Nat)
  | unbounded
  deriving DecidableEq, Repr

/-- The half-open token range `[s, e)` as a pointer. The release, and its own
unit tests, require the start to name an existing token: `1..1` on a
one-token pointer and `0..0` on the root are `None`, while `0..0` on a
one-token pointer is the root. -/
def getRange (xs : List Nat) (s e : Nat) : Option (List Nat) :=
  let ts := encodedTokens xs
  if s ≤ e ∧ s < ts.length ∧ e ≤ ts.length then
    some (renderEncoded ((ts.drop s).take (e - s)))
  else none

/-- `Pointer::get(s..)`. -/
def getRangeFrom (xs : List Nat) (s : Nat) : Option (List Nat) :=
  let ts := encodedTokens xs
  if s < ts.length then some (renderEncoded (ts.drop s)) else none

/-- `Pointer::get(..e)`. Unlike the other forms, `..0` succeeds on the root. -/
def getRangeTo (xs : List Nat) (e : Nat) : Option (List Nat) :=
  let ts := encodedTokens xs
  if e ≤ ts.length then some (renderEncoded (ts.take e)) else none

/-- `Pointer::get(s..=e)`. -/
def getRangeIncl (xs : List Nat) (s e : Nat) : Option (List Nat) :=
  if s ≤ e ∧ e < count xs then getRange xs s (e + 1) else none

/-- `Pointer::get(..=e)`. -/
def getRangeToIncl (xs : List Nat) (e : Nat) : Option (List Nat) :=
  if e < count xs then getRangeTo xs (e + 1) else none

/-- INTENDED `Pointer::get((start, end))`. An excluded start `n` means the
natural number `n + 1`, with no machine wrap-around. The release computes a
machine successor, so this contract is refuted at `Excluded(usize::MAX)`
(JSONPTR-002). -/
def getBounds (xs : List Nat) : Bound → Bound → Option (List Nat)
  | .included s, .included e => getRangeIncl xs s e
  | .included s, .excluded e => getRange xs s e
  | .included s, .unbounded => getRangeFrom xs s
  | .excluded s, .included e => getRangeIncl xs (s + 1) e
  | .excluded s, .excluded e => getRange xs (s + 1) e
  | .excluded s, .unbounded => getRangeFrom xs (s + 1)
  | .unbounded, .included e => getRangeToIncl xs e
  | .unbounded, .excluded e => getRangeTo xs e
  | .unbounded, .unbounded => some xs

/-! ## Token-sequence comparison (§9) -/

/-- Executable prefix test on token lists. -/
def isTokenPrefix : List (List Nat) → List (List Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, t :: ts => decide (p = t) && isTokenPrefix ps ts

/-- `Pointer::starts_with`: `other`'s tokens are a prefix of `self`'s. -/
def startsWith (self other : List Nat) : Bool :=
  isTokenPrefix (encodedTokens other) (encodedTokens self)

/-- Token-suffix test. -/
def isTokenSuffix (s ts : List (List Nat)) : Bool := isTokenPrefix s.reverse ts.reverse

/-- `Pointer::ends_with`. As documented, the root is a suffix only of itself. -/
def endsWith (self other : List Nat) : Bool :=
  if other = [] then decide (self = []) else isTokenSuffix (encodedTokens other) (encodedTokens self)

/-- INTENDED `Pointer::strip_prefix`: defined exactly when `starts_with` holds,
and then the remaining tokens. The release tests a raw string prefix, so this
contract is refuted (JSONPTR-001): `"/ab"` minus `"/a"` gives `Some("b")`. -/
def stripPrefix (self pre : List Nat) : Option (List Nat) :=
  if startsWith self pre then
    some (renderEncoded ((encodedTokens self).drop (encodedTokens pre).length))
  else none

/-- `Pointer::strip_suffix`. The root suffix is accepted for every pointer,
although `ends_with` rejects it for a non-root pointer. -/
def stripSuffix (self suf : List Nat) : Option (List Nat) :=
  let ts := encodedTokens self
  let ss := encodedTokens suf
  if isTokenSuffix ss ts then some (renderEncoded (ts.take (ts.length - ss.length))) else none

/-- Longest common prefix of two token lists. -/
def commonPrefix : List (List Nat) → List (List Nat) → List (List Nat)
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

/-- `Pointer::intersection`. -/
def intersection (self other : List Nat) : List Nat :=
  renderEncoded (commonPrefix (encodedTokens self) (encodedTokens other))

/-- Lexicographic order on byte lists: the order of `Pointer`, `PointerBuf`
and `Token` (derived on the encoded string). It is not a token-wise order. -/
def bytesLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a < b) || (decide (a = b) && bytesLt as bs)

/-! ## Buffer mutation (§10)

Each function returns the final buffer; tokens are already encoded. -/

/-- `PointerBuf::from_tokens`. -/
def fromTokens (ts : List (List Nat)) : List Nat := renderEncoded ts

/-- `PointerBuf::push_front`, `Pointer::with_leading_token`. -/
def pushFront (xs t : List Nat) : List Nat := 47 :: (t ++ xs)

/-- `PointerBuf::push_back`, `Pointer::with_trailing_token`. -/
def pushBack (xs t : List Nat) : List Nat := xs ++ 47 :: t

/-- `PointerBuf::pop_back`: final buffer and removed token. -/
def popBack (xs : List Nat) : List Nat × Option (List Nat) :=
  match splitBack xs with
  | none => (xs, none)
  | some (p, t) => (p, some t)

/-- `PointerBuf::pop_front`: final buffer and removed token. -/
def popFront (xs : List Nat) : List Nat × Option (List Nat) :=
  match splitFront xs with
  | none => (xs, none)
  | some (t, rest) => (rest, some t)

/-- `PointerBuf::append`, `Pointer::concat`: byte concatenation. The release
special-cases a root on either side; both cases equal concatenation. -/
def append (xs other : List Nat) : List Nat := xs ++ other

/-- Payload of `ReplaceError`. -/
structure ReplaceError where
  index : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- `PointerBuf::replace`: final buffer and the replaced token. On error the
buffer is unchanged; the error carries the supplied index and the token count
(0 for the root). Success always returns `Some`. -/
def replaceToken (xs : List Nat) (index : Nat) (t : List Nat) :
    Res ReplaceError (List Nat × List Nat) :=
  let ts := encodedTokens xs
  match ts[index]? with
  | none => .error ⟨index, ts.length⟩
  | some old => .ok (renderEncoded (ts.set index t), old)

/-! ## Token and index odds and ends (§11) -/

/-- `Token::is_next`. -/
def isNext (encoded : List Nat) : Bool := decide (encoded = [45])

/-- `Index::for_len_incl` (inclusive bound), restated from the default profile. -/
def forLenIncl (i : Index) (length : Nat) : Res OutOfBounds Nat :=
  match i with
  | .num n => if n ≤ length then .ok n else .error ⟨length, n⟩
  | .next => .ok length

/-- `Index::for_len_unchecked`. -/
def forLenUnchecked (i : Index) (length : Nat) : Nat :=
  match i with
  | .num n => n
  | .next => length

/-! ## Mutable resolution, assignment, deletion over the tree (§12–§14) -/

/-- Replace the value of the first entry for `k`. -/
def setKey (k : List Nat) (v : Tree) : List (List Nat × Tree) → List (List Nat × Tree)
  | [] => []
  | (k', v') :: rest => if k' = k then (k', v) :: rest else (k', v') :: setKey k v rest

/-- Remove the first entry for `k`. -/
def eraseKey (k : List Nat) : List (List Nat × Tree) → List (List Nat × Tree)
  | [] => []
  | (k', v') :: rest => if k' = k then rest else (k', v') :: eraseKey k rest

/-- The document after writing `new` through the reference that `resolve_mut`
returns for `keys`. `none` exactly when resolution fails. Every node off the
path is unchanged. -/
def replaceAt (usizeMax : Nat) (t : Tree) : List (List Nat) → Tree → Option Tree
  | [], new => some new
  | k :: ks, new =>
    match t with
    | .arr items =>
      match parseIndex usizeMax (encode k) with
      | .error _ => none
      | .ok i =>
        match forLen i items.length with
        | .error _ => none
        | .ok n =>
          match items[n]? with
          | none => none
          | some child =>
            (replaceAt usizeMax child ks new).map (fun c => .arr (items.set n c))
    | .obj members =>
      match lookupKey k members with
      | none => none
      | some child => (replaceAt usizeMax child ks new).map (fun c => .obj (setKey k c members))
    | .leaf _ => none

/-- Path expansion used by assignment: wrap `v` in one container per remaining
key, outermost first. A key spelled `0` or `-` makes a one-item array; any
other key, including `1`, makes a one-member object. -/
def expand : List (List Nat) → Tree → Tree
  | [], v => v
  | k :: ks, v =>
    if k = [48] ∨ k = [45] then .arr [expand ks v] else .obj [(k, expand ks v)]

/-- Payload of `assign::Error`. -/
inductive AssignError where
  | failedToParseIndex (position offset : Nat) (source : IndexError)
  | outOfBounds (position offset : Nat) (source : OutOfBounds)
  deriving DecidableEq, Repr

/-- `Assign::assign`: the final document and the replaced value.

* no keys left: replace the node, return it;
* array, index below the length: descend;
* array, index equal to the length (numeric or `-`): push the expansion of the
  remaining keys, return `none`;
* object, key present: descend; key absent: add the member with the expansion
  of the remaining keys, at the end of the member list, return `none`;
* scalar with keys left: replace it by the expansion of all remaining keys,
  including the current one, and return the old scalar.

On error the document is unchanged (no `Tree` is returned). -/
def assignFrom (usizeMax : Nat) (position offset : Nat) (t : Tree) :
    List (List Nat) → Tree → Res AssignError (Tree × Option Tree)
  | [], v => .ok (v, some t)
  | k :: ks, v =>
    let next := offset + 1 + (encode k).length
    match t with
    | .arr items =>
      match parseIndex usizeMax (encode k) with
      | .error e => .error (.failedToParseIndex position offset e)
      | .ok i =>
        match forLenIncl i items.length with
        | .error e => .error (.outOfBounds position offset e)
        | .ok n =>
          match items[n]? with
          | none => .ok (.arr (items ++ [expand ks v]), none)
          | some child =>
            match assignFrom usizeMax (position + 1) next child ks v with
            | .error e => .error e
            | .ok (c, old) => .ok (.arr (items.set n c), old)
    | .obj members =>
      match lookupKey k members with
      | none => .ok (.obj (members ++ [(k, expand ks v)]), none)
      | some child =>
        match assignFrom usizeMax (position + 1) next child ks v with
        | .error e => .error e
        | .ok (c, old) => .ok (.obj (setKey k c members), old)
    | .leaf _ => .ok (expand (k :: ks) v, some t)

def assign (usizeMax : Nat) (root : Tree) (keys : List (List Nat)) (v : Tree) :
    Res AssignError (Tree × Option Tree) :=
  assignFrom usizeMax 0 0 root keys v

/-- `Delete::delete`: the final document and the removed value. `rootRepl` is
what the root becomes when the pointer is empty: JSON null, or an empty TOML
table. Every failure leaves the document unchanged and returns `none`. -/
def delete (usizeMax : Nat) (rootRepl root : Tree) (keys : List (List Nat)) :
    Tree × Option Tree :=
  match keys.getLast? with
  | none => (rootRepl, some root)
  | some last =>
    let parentKeys := keys.dropLast
    match resolve usizeMax root parentKeys with
    | .error _ => (root, none)
    | .ok (.leaf _) => (root, none)
    | .ok (.arr items) =>
      match parseIndex usizeMax (encode last) with
      | .error _ => (root, none)
      | .ok i =>
        match forLen i items.length with
        | .error _ => (root, none)
        | .ok n =>
          match items[n]? with
          | none => (root, none)
          | some old =>
            ((replaceAt usizeMax root parentKeys (.arr (items.eraseIdx n))).getD root, some old)
    | .ok (.obj members) =>
      match lookupKey last members with
      | none => (root, none)
      | some old =>
        ((replaceAt usizeMax root parentKeys (.obj (eraseKey last members))).getD root, some old)

/-! ## Error inspection and diagnostic spans (§15–§16)

Spans are byte offsets and byte lengths in the subject. -/

/-- `ParseError::pointer_offset` / `offset`. -/
def ptrErrPointerOffset : PtrError → Nat
  | .noLeadingSlash => 0
  | .invalidEncoding d _ => d

/-- `ParseError::source_offset`. -/
def ptrErrSourceOffset : PtrError → Nat
  | .noLeadingSlash => 0
  | .invalidEncoding _ t => t

/-- `ParseError::complete_offset`, as a natural number. The machine sum fits
for every parser-produced error; it can overflow for a hand-built one (N7). -/
def ptrErrCompleteOffset (e : PtrError) : Nat := ptrErrPointerOffset e + ptrErrSourceOffset e

/-- INTENDED `ParseError::invalid_encoding_len` for an error produced by
parsing `subject`: 2 when a byte follows the offending tilde, otherwise 1; 0
for `NoLeadingSlash`. Refuted by the release (JSONPTR-003). -/
def invalidEncodingLen (e : PtrError) (subject : List Nat) : Nat :=
  match e with
  | .noLeadingSlash => 0
  | .invalidEncoding d t => if d + t + 1 < subject.length then 2 else 1

/-- RELEASE behaviour of `invalid_encoding_len` on a nonempty subject, kept
only so the refutation can be stated: it compares the separator position, not
the tilde position. On an empty subject the release underflows (N5). -/
def invalidEncodingLenRelease (e : PtrError) (subject : List Nat) : Nat :=
  match e with
  | .noLeadingSlash => 0
  | .invalidEncoding d _ => if d < subject.length - 1 then 2 else 1

/-- A diagnostic span. The label text is not modelled. -/
structure Span where
  offset : Nat
  len : Nat
  deriving DecidableEq, Repr

/-- INTENDED `ParseError::labels`. -/
def ptrErrLabel (e : PtrError) (subject : List Nat) : Span :=
  ⟨ptrErrCompleteOffset e, invalidEncodingLen e subject⟩

/-- `EncodingError::labels` for an error with `1 ≤ offset` when the source is
`Tilde`: a pending tilde at the end is labelled at the tilde itself. With
`offset = 0`, `Tilde` and an empty subject the release underflows (N8). -/
def encErrLabel (e : EncError) (subject : List Nat) : Span :=
  match e.source with
  | .slash => ⟨e.offset, 1⟩
  | .tilde => if e.offset = subject.length then ⟨e.offset - 1, 1⟩ else ⟨e.offset, 1⟩

/-- Number of leading bytes satisfying `p`. -/
def countWhile (p : Nat → Bool) : List Nat → Nat
  | [] => 0
  | b :: rest => if p b then 1 + countWhile p rest else 0

/-- INTENDED `ParseIndexError::labels`, as a predicate because the documented
intent does not fix the length for an all-zero subject.

* `InvalidInteger`: no label.
* `LeadingZeros`: offset 0; the length is the number of leading `0` bytes when
  a non-zero byte follows, and otherwise any length from 1 to the subject
  length. The release panics on an all-zero subject (N1).
* `InvalidCharacter off`: offset `off`; the length is the number of bytes from
  `off` up to the next ASCII digit or the end. The release counts characters
  and falls back to the whole subject length (N2). -/
def IndexErrLabelPost (e : IndexError) (subject : List Nat) : Option Span → Prop
  | none => ∃ k, e = .invalidInteger k
  | some sp =>
    match e with
    | .invalidInteger _ => False
    | .leadingZeros =>
      sp.offset = 0 ∧
        (if countWhile (fun b => b == 48) subject < subject.length
         then sp.len = countWhile (fun b => b == 48) subject
         else 1 ≤ sp.len ∧ sp.len ≤ subject.length)
    | .invalidCharacter off =>
      sp.offset = off ∧ sp.len = countWhile (fun b => !isDigit b) (subject.drop off)

/-- `resolve::Error::labels` and `assign::Error::labels`, given the error's
`position` and `offset` and the pointer it came from: no label when the
pointer has no token at `position`; otherwise the span starts just after the
separator and covers the token, except that for a separator in the last byte
the span starts at the separator. Requires `offset + 1 ≤ usize::MAX` (N6). -/
def tokenErrLabel (position offset : Nat) (origin : List Nat) : Option Span :=
  match getToken origin position with
  | none => none
  | some tok => some ⟨if offset + 1 < origin.length then offset + 1 else offset, tok.length⟩

/-! ## Closed test vectors for the extension

Each agrees with the native release in the debug and release profiles, except
where marked INTENDED. -/

theorem tv_count_root : count [] = 0 := by decide
theorem tv_count_two_empty : count [47, 47] = 2 := by decide
/-- `"/a/b"`. -/
theorem tv_split_front : splitFront [47, 97, 47, 98] = some ([97], [47, 98]) := by decide
theorem tv_split_back : splitBack [47, 97, 47, 98] = some ([47, 97], [98]) := by decide
theorem tv_split_back_root : splitBack [] = none := by decide
/-- `"/"`: one empty token, parent is the root. -/
theorem tv_split_back_slash : splitBack [47] = some ([], []) := by decide
theorem tv_split_at_zero : splitAtOffset [47, 120] 0 = some ([], [47, 120]) := by decide
theorem tv_split_at_root : splitAtOffset [] 0 = none := by decide

theorem tv_range_0_0_root : getRange [] 0 0 = none := by decide
theorem tv_range_0_0_slash : getRange [47] 0 0 = some [] := by decide
theorem tv_range_1_1_slash : getRange [47] 1 1 = none := by decide
theorem tv_range_1_1_two : getRange [47, 97, 47, 98] 1 1 = some [] := by decide
theorem tv_range_2_2_two : getRange [47, 97, 47, 98] 2 2 = none := by decide
theorem tv_range_from_end : getRangeFrom [47, 97, 47, 98] 2 = none := by decide
theorem tv_range_to_0_root : getRangeTo [] 0 = some [] := by decide
theorem tv_range_incl : getRangeIncl [47, 97, 47, 98] 0 0 = some [47, 97] := by decide
theorem tv_range_to_incl : getRangeToIncl [47, 97, 47, 98] 1 = some [47, 97, 47, 98] := by decide
theorem tv_bounds_excl : getBounds [47, 97, 47, 98] (.excluded 0) .unbounded = some [47, 98] := by decide

/-- `"/a/b"` against `"/b"`. -/
theorem tv_ends_with : endsWith [47, 97, 47, 98] [47, 98] = true := by decide
/-- `"/ab"` against `"/b"`: a string suffix inside a token does not count. -/
theorem tv_ends_with_partial : endsWith [47, 97, 98] [47, 98] = false := by decide
theorem tv_ends_with_root : endsWith [47, 97] [] = false := by decide
theorem tv_strip_suffix_root : stripSuffix [47, 97] [] = some [47, 97] := by decide
theorem tv_strip_suffix : stripSuffix [47, 97, 47, 98] [47, 98] = some [47, 97] := by decide
theorem tv_starts_with_partial : startsWith [47, 97, 98] [47, 97] = false := by decide
/-- INTENDED; the release returns `Some("b")` (JSONPTR-001). -/
theorem tv_strip_prefix_partial : stripPrefix [47, 97, 98] [47, 97] = none := by decide
theorem tv_strip_prefix : stripPrefix [47, 97, 47, 98] [47, 97] = some [47, 98] := by decide
/-- `"/a/b"` and `"/a/c"`. -/
theorem tv_intersection : intersection [47, 97, 47, 98] [47, 97, 47, 99] = [47, 97] := by decide
theorem tv_intersection_longer : intersection [47, 97] [47, 97, 47, 98] = [47, 97] := by decide

/-- `"/~0/a~1b/"` with token 1 replaced by `z`. -/
theorem tv_replace :
    replaceToken [47, 126, 48, 47, 97, 126, 49, 98, 47] 1 [122] =
      .ok ([47, 126, 48, 47, 122, 47], [97, 126, 49, 98]) := by decide
theorem tv_replace_root : replaceToken [] 3 [120] = .error ⟨3, 0⟩ := by decide
theorem tv_replace_oob : replaceToken [47, 97] 1 [120] = .error ⟨1, 1⟩ := by decide
theorem tv_pop_back_slash : popBack [47] = ([], some []) := by decide
theorem tv_pop_front : popFront [47, 97, 47, 98] = ([47, 98], some [97]) := by decide

/-- `{"a": 1}` assigned at `/b/0/c` then token `-` then `1`:
`{"a":1,"b":[{"c":[{"1":V}]}]}`, nothing replaced. -/
theorem tv_assign_expand :
    assign 255 (.obj [([97], .leaf 1)]) [[98], [48], [99], [45], [49]] (.leaf 9) =
      .ok (.obj [([97], .leaf 1),
        ([98], .arr [.obj [([99], .arr [.obj [([49], .leaf 9)]])]])], none) := by rfl
/-- `{"a": 1}` at `/a/x`: the scalar is replaced by `{"x": V}` and returned. -/
theorem tv_assign_scalar :
    assign 255 (.obj [([97], .leaf 1)]) [[97], [120]] (.leaf 9) =
      .ok (.obj [([97], .obj [([120], .leaf 9)])], some (.leaf 1)) := by rfl
/-- `{"a": [1, 2]}` at `/a/2`: appended. -/
theorem tv_assign_push :
    assign 255 (.obj [([97], .arr [.leaf 1, .leaf 2])]) [[97], [50]] (.leaf 9) =
      .ok (.obj [([97], .arr [.leaf 1, .leaf 2, .leaf 9])], none) := by rfl
/-- `{"a": [1, 2]}` at `/a/3`: `OutOfBounds` at position 1, offset 2. -/
theorem tv_assign_oob :
    assign 255 (.obj [([97], .arr [.leaf 1, .leaf 2])]) [[97], [51]] (.leaf 9) =
      .error (.outOfBounds 1 2 ⟨2, 3⟩) := by rfl
theorem tv_assign_root :
    assign 255 (.leaf 1) [] (.leaf 9) = .ok (.leaf 9, some (.leaf 1)) := by rfl

/-- `{"a": [1, 2, 3]}` at `/a/0`. -/
theorem tv_delete_item :
    delete 255 (.leaf 0) (.obj [([97], .arr [.leaf 1, .leaf 2, .leaf 3])]) [[97], [48]] =
      (.obj [([97], .arr [.leaf 2, .leaf 3])], some (.leaf 1)) := by rfl
theorem tv_delete_member :
    delete 255 (.leaf 0) (.obj [([97], .leaf 1), ([98], .leaf 2)]) [[97]] =
      (.obj [([98], .leaf 2)], some (.leaf 1)) := by rfl
theorem tv_delete_root :
    delete 255 (.leaf 0) (.obj [([97], .leaf 1)]) [] =
      (.leaf 0, some (.obj [([97], .leaf 1)])) := by rfl
/-- Token `-` never names an existing item. -/
theorem tv_delete_next :
    delete 255 (.leaf 0) (.obj [([97], .arr [.leaf 1])]) [[97], [45]] =
      (.obj [([97], .arr [.leaf 1])], none) := by rfl

/-- `"/a/"` failing at position 1, offset 2: the span sits on the separator. -/
theorem tv_label_last_empty : tokenErrLabel 1 2 [47, 97, 47] = some ⟨2, 0⟩ := by decide
theorem tv_label_token : tokenErrLabel 0 0 [47, 98, 47, 99] = some ⟨1, 1⟩ := by decide
/-- `"/~"`: INTENDED length 1; the release reports 2 (JSONPTR-003). -/
theorem tv_len_final_tilde : invalidEncodingLen (.invalidEncoding 0 1) [47, 126] = 1 := by decide
theorem tv_len_final_tilde_release :
    invalidEncodingLenRelease (.invalidEncoding 0 1) [47, 126] = 2 := by decide

/-! ## Sanity obligations for the extension (draft only) -/

/-- SANITY OBLIGATION. Splitting at the front and rejoining loses nothing. -/
theorem splitFront_spec (xs t rest : List Nat) (hv : ValidPointer xs)
    (h : splitFront xs = some (t, rest)) : xs = 47 :: (t ++ rest) ∧ ValidPointer rest := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Likewise at the back. -/
theorem splitBack_spec (xs p t : List Nat) (hv : ValidPointer xs)
    (h : splitBack xs = some (p, t)) : xs = p ++ 47 :: t ∧ ValidPointer p := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Every range result is a valid pointer whose bytes are a
contiguous part of the input. -/
theorem getRange_valid (xs : List Nat) (s e : Nat) (r : List Nat) (hv : ValidPointer xs)
    (h : getRange xs s e = some r) : ValidPointer r ∧ ∃ a b, xs = a ++ r ++ b := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. A byte split at a slash yields two valid pointers. -/
theorem splitAtOffset_valid (xs h t : List Nat) (off : Nat) (hv : ValidPointer xs)
    (hs : splitAtOffset xs off = some (h, t)) :
    ValidPointer h ∧ ValidPointer t ∧ xs = h ++ t := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `starts_with` is the string test the release performs. -/
theorem startsWith_iff (self other : List Nat) (hs : ValidPointer self)
    (ho : ValidPointer other) :
    startsWith self other = true ↔
      (∃ rest, self = other ++ rest ∧ (rest = [] ∨ rest.head? = some 47)) := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `strip_suffix` on tokens is the raw string suffix
removal the release performs, so the release meets this contract. -/
theorem stripSuffix_iff (self suf r : List Nat) (hs : ValidPointer self)
    (hf : ValidPointer suf) : stripSuffix self suf = some r ↔ self = r ++ suf := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The intended `strip_prefix` returns a valid pointer. -/
theorem stripPrefix_valid (self pre r : List Nat) (hs : ValidPointer self)
    (hp : ValidPointer pre) (h : stripPrefix self pre = some r) :
    ValidPointer r ∧ self = pre ++ r := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The intersection is a prefix of both pointers. -/
theorem intersection_startsWith (a b : List Nat) (ha : ValidPointer a) (hb : ValidPointer b) :
    startsWith a (intersection a b) = true ∧ startsWith b (intersection a b) = true := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Mutators preserve the representation invariant and act
on the token list as named. -/
theorem pushBack_tokens (xs t : List Nat) (hv : ValidPointer xs) (ht : ValidEncodedToken t) :
    ValidPointer (pushBack xs t) ∧
      encodedTokens (pushBack xs t) = encodedTokens xs ++ [t] := by
  sorry -- spec sanity obligation, draft only

theorem pushFront_tokens (xs t : List Nat) (hv : ValidPointer xs) (ht : ValidEncodedToken t) :
    ValidPointer (pushFront xs t) ∧
      encodedTokens (pushFront xs t) = t :: encodedTokens xs := by
  sorry -- spec sanity obligation, draft only

theorem append_tokens (xs ys : List Nat) (hx : ValidPointer xs) (hy : ValidPointer ys) :
    ValidPointer (append xs ys) ∧
      encodedTokens (append xs ys) = encodedTokens xs ++ encodedTokens ys := by
  sorry -- spec sanity obligation, draft only

theorem replaceToken_valid (xs t r old : List Nat) (i : Nat) (hv : ValidPointer xs)
    (ht : ValidEncodedToken t) (h : replaceToken xs i t = .ok (r, old)) :
    ValidPointer r ∧ encodedTokens r = (encodedTokens xs).set i t ∧
      (encodedTokens xs)[i]? = some old := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. `replaceAt` succeeds exactly when resolution does, and
writing back the resolved node changes nothing. -/
theorem replaceAt_isSome_iff (usizeMax : Nat) (root new : Tree) (keys : List (List Nat)) :
    (replaceAt usizeMax root keys new).isSome ↔ ∃ node, resolve usizeMax root keys = .ok node := by
  sorry -- spec sanity obligation, draft only

theorem replaceAt_self (usizeMax : Nat) (root node : Tree) (keys : List (List Nat))
    (h : resolve usizeMax root keys = .ok node) : replaceAt usizeMax root keys node = some root := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. After a write, the path resolves to the written node,
provided no object on the path has a duplicate of the key used. (First-match
lookup makes this hold without that proviso as well.) -/
theorem resolve_replaceAt (usizeMax : Nat) (root new doc : Tree) (keys : List (List Nat))
    (h : replaceAt usizeMax root keys new = some doc) : resolve usizeMax doc keys = .ok new := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. When assignment replaces an existing node, it is the
node resolution selects and the result is the write-back. -/
theorem assign_existing (usizeMax : Nat) (root v old : Tree) (keys : List (List Nat))
    (h : resolve usizeMax root keys = .ok old) :
    ∃ doc, replaceAt usizeMax root keys v = some doc ∧
      assign usizeMax root keys v = .ok (doc, some old) := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Assignment errors come only from arrays and carry a
position and offset that name a token, as for resolution. -/
theorem assign_error_location (usizeMax : Nat) (root v : Tree) (keys : List (List Nat))
    (err : AssignError) (h : assign usizeMax root keys v = .error err) :
    ∃ position offset,
      ((∃ e, err = .failedToParseIndex position offset e) ∨
        (∃ e, err = .outOfBounds position offset e)) ∧
      position < keys.length ∧ offset = (render (keys.take position)).length := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. Deletion removes a node exactly when a non-root pointer
resolves, and then returns that node. -/
theorem delete_some_iff (usizeMax : Nat) (rootRepl root old : Tree) (keys : List (List Nat))
    (hk : keys ≠ []) :
    (delete usizeMax rootRepl root keys).2 = some old ↔ resolve usizeMax root keys = .ok old := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. A failed deletion leaves the document unchanged. -/
theorem delete_none_unchanged (usizeMax : Nat) (rootRepl root : Tree) (keys : List (List Nat))
    (h : (delete usizeMax rootRepl root keys).2 = none) :
    (delete usizeMax rootRepl root keys).1 = root := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. For a parser-produced error the intended span lies
inside the subject, and the complete offset is the offending tilde. -/
theorem ptrErrLabel_in_bounds (xs : List Nat) (d t : Nat)
    (h : pointerError xs = some (.invalidEncoding d t)) :
    xs[d + t]? = some 126 ∧
      d + t + invalidEncodingLen (.invalidEncoding d t) xs ≤ xs.length := by
  sorry -- spec sanity obligation, draft only

/-- SANITY OBLIGATION. The release length differs from the intended one for a
final tilde in a token that is not the whole input tail, e.g. `"/~"`. This is
the statement of JSONPTR-003 inside the model. -/
theorem invalidEncodingLen_release_differs :
    invalidEncodingLenRelease (.invalidEncoding 0 1) [47, 126] ≠
      invalidEncodingLen (.invalidEncoding 0 1) [47, 126] := by decide

/-- SANITY OBLIGATION. For an error produced by `from_encoded`, the label is a
one-byte span inside a nonempty subject. -/
theorem encErrLabel_in_bounds (e : List Nat) (err : EncError) (h : firstEncError e = some err) :
    (encErrLabel err e).offset + (encErrLabel err e).len ≤ e.length := by
  sorry -- spec sanity obligation, draft only

end JsonptrSpecModel
