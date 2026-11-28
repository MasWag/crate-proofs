import SpecModel

/-!
# jsonptr 0.8.2 specification model, extension part (scratch port)

Verbatim copy of the extension part (specification sections 8-20) of
`aeneas/profiles/adapted/spec-draft/SpecModel.lean`
(SHA-256 `22891f76bd5959f5b1b45e529cf16b48889594691a178071ce02a4159499044e`),
from the heading "Extension: the remaining public API" up to, not including,
"Sanity obligations for the extension (draft only)". Copied by the
implementation agent; the unproved sanity obligations are omitted.
-/

namespace JsonptrSpecModel

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


end JsonptrSpecModel
