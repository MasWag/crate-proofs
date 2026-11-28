# jsonptr 0.8.2 adapted-profile contracts

The specification agent wrote this document independently of proof work, before any
adapted source or generated Lean existed. It refines the
[default specification](../default/specification.md) for the core algorithms whose release
bodies do not extract with the unchanged verifier. It does not replace or weaken the
default contracts. The executable model is in
[spec-draft/SpecModel.lean](spec-draft/SpecModel.lean); the discrepancies noticed while
writing it are in [spec-draft/NOTES.md](spec-draft/NOTES.md).

Syntax and read semantics follow [RFC 6901 §3](https://www.rfc-editor.org/rfc/rfc6901#section-3)
and [§4](https://www.rfc-editor.org/rfc/rfc6901#section-4). Error payloads come from the
release source in `.work/source/src`.

## What a theorem in this profile is about

The subject of every theorem here is an adapted function: a byte-slice, explicit-index
rewrite of a release body, produced by a recorded patch. A closed theorem establishes the
contract for that adapted function. It establishes the release API only together with the
correspondence obligations in [Release correspondence](#release-correspondence), which
Lean does not check. No public API may be mapped to an adapted theorem as verified.

## Conventions

- A string is its UTF-8 byte list. `E` is `encode` in the model: `/` (47) becomes `~1`,
  `~` (126) becomes `~0`, every other byte is kept. Because 47 and 126 are ASCII, the
  bytewise `E` equals the characterwise one.
- Each contract is total success: for every input in the domain there is an output with
  `f input = ok out` and the stated property. A Rust `Err` is an `ok` outcome carrying
  the exact error value. A panic or a failed machine operation is never acceptable.
- The domain is every byte slice, with no UTF-8 premise and no content restriction, and
  every `usize` including 0 and `usize::MAX`. The one permitted premise is the Rust slice
  invariant `len ≤ isize::MAX`, used only where the release itself computes `len + 1` or
  builds a longer output. State it explicitly in each theorem that uses it.
- Offsets count bytes from 0 in the argument of the operation.

## Targets in priority order

No target below deviates from RFC 6901 or from the crate's functional documentation, as
far as source inspection and native probes show. The discrepancies found are in
documentation and diagnostics; the notes list them.

### 1. Pointer validation wrapper — `pointer::validate` (`pointer.rs:1355`)

Input: a byte slice `xs`, empty included. Output: success, or a `ParseError`.

Contract: for every `xs` the function succeeds with the outcome `pointerError xs`.

- `none`: accepted. The accepted set is exactly the renderings of key lists
  (`pointerError_none_iff`). The empty slice is accepted as the root, by the wrapper's own
  branch and without calling the kernel. The success value is the unchanged input.
- `NoLeadingSlash`: `xs` is nonempty and its first byte is not 47. This takes precedence
  over any bad escape, so `"~"` gives `NoLeadingSlash`.
- `InvalidEncoding { offset: d, source: EncodingError { offset: t, source: Tilde } }`:
  `j = d + t` is the first tilde not followed by ASCII `0` or `1`, and `d` is the last
  slash before `j`. For `"/x/a~"`, `d = 2` and `t = 2`.

`PointerPost` states the same contract declaratively and determines the outcome uniquely.
The default profile already proves the kernel `validate_bytes` on nonempty input at
offset zero. This target adds the empty branch and the lift to the wrapper's return type.

Not covered: `Pointer::parse`, `PointerBuf::parse`, `from_static`, `FromStr` and `TryFrom`
construct their results with reference casts, `into_report` or a `const` assertion that
this target does not model.

### 2. Token encoding — `Token::new` then `encoded` (`token.rs:128`)

Input: a byte slice `x` with `len ≤ isize::MAX`. Output: the encoded bytes and whether the
input was reused.

Contract: the encoded bytes equal `encode x`. The input is reused without building a new
buffer exactly when `needsNoEncoding x`, that is, when no byte is 47 or 126. In the
release this is the difference between returning the caller's `Cow` and a new
`Cow::Owned`. `"~1"` encodes to `"~01"`.

### 3. Token decoding — `Token::decoded` (`token.rs:224`)

Input: a byte slice `e` with `len ≤ isize::MAX`. Output: the decoded bytes and whether the
input was reused.

Contract: the function succeeds on every `e`. If `ValidEncodedToken e`, the output is the
unique `x` with `encode x = e`, which is `decode? e`. The input is reused exactly when `e`
contains no byte 126.

The contract does not constrain the output for `e` outside the image of `E`; only success
is required there. A lawful `Token` never holds such bytes. The release maps `"~a0"` to
`"a~"` on such input; that is recorded, not specified.

### 4. Encoded-token validation — `Token::from_encoded` (`token.rs:77`)

Input: a byte slice `e`. Output: success, or an `EncodingError`.

Contract: for every `e` the outcome is `firstEncError e`.

- `none`: accepted with the bytes unchanged, exactly when `ValidEncodedToken e`.
- A slash outside an escape gives `Slash` at the slash.
- A tilde followed by a slash gives `Slash` at that slash: `"~/"` gives offset 1.
- A tilde followed by any other byte except `0` and `1`, including a second tilde, gives
  `Tilde` at that following byte: `"a~b"` gives offset 2.
- A final tilde gives `Tilde` at `len`: `"a~"` gives offset 2.

A `Tilde` offset is therefore one past the offending tilde. The field documentation says
it is the offset of the tilde; see candidate N4 in the notes. The numeric value is the
intended one, because `EncodingError::labels` and the pointer parser both rely on it:
`pointerError_token_agrees` states that a pointer error and the error of its offending
token carry the same number.

### 5. Index parsing — `Index::from_str`, `Token::to_index` (`index.rs:166`)

Input: a byte slice `s`. Output: an `Index`, or a `ParseIndexError`.

Contract: for every `s` the outcome is `parseIndex usize::MAX s`, with this precedence.

1. `s` is exactly `-`: `Next`.
2. `s` starts with `0` and is longer than `"0"`: `LeadingZeros`. This holds even when a
   later byte is not a digit, so `"0a"` gives `LeadingZeros`.
3. Some byte is not an ASCII digit: `InvalidCharacter` at the first such byte. `"+1"` and
   `"-1"` give offset 0. The release counts characters; the two counts agree because
   every earlier byte is an ASCII digit.
4. `s` is empty: `InvalidInteger` of kind `Empty`.
5. The decimal value exceeds `usize::MAX`: `InvalidInteger` of kind `PosOverflow`.
6. Otherwise `Num` of the decimal value. `usize::MAX` itself is accepted.

Success with `Num` coincides with the RFC 6901 §4 `array-index` grammar plus the
machine-word bound (`parseIndex_ok_iff`). `to_index` applies the same function to the
encoded token; `parseIndex_encode` states that this equals parsing the decoded key.

The observation of `InvalidInteger` is the error kind only. Code outside the standard
library cannot construct a `ParseIntError`, so an adapted body must report the kind
through its own type.

### 6. Token splitting — `Pointer::split_front`, `Pointer::tokens` (`pointer.rs:181`, `:120`)

Input: a byte slice `xs` that is empty or starts with 47. Output: for `split_front`,
nothing on empty input, otherwise the first token and the remainder.

Contract: on nonempty input the first token is the bytes after the leading slash up to the
next slash or the end, and the remainder starts at that next slash or is empty. The token
followed by the remainder's tokens equals `encodedTokens xs`, and no byte is lost
(`renderEncoded_encodedTokens`). `"//"` has two empty tokens; `""` has none.

The premise on the first byte is the `Pointer` representation invariant. Target 1 is the
producer obligation for it.

### 7. Resolution — JSON `Resolve::resolve` (`resolve.rs:283`)

Input: a document and a pointer. Output: the selected node, or a `resolve::Error`.

Contract, over the specification tree: the outcome is `resolve usize::MAX root keys`,
where `keys` are the decoded tokens of the pointer.

- No tokens left: the current node. The empty pointer selects the root.
- At an array: parse the encoded token as in target 5. A parse error gives
  `FailedToParseIndex` with that cause. Otherwise apply the strict bound; failure gives
  `OutOfBounds { length, index }`, and `-` always fails with `index = length`. Otherwise
  continue at that item.
- At an object: look up the decoded key by exact byte equality. Absence gives `NotFound`.
- At a scalar with a token left: `Unreachable`.
- Every error carries `position`, the zero-based index of the failing token, and
  `offset`, the byte position of the separator opening it, which is the sum of
  `1 + len(E(key))` over the earlier keys.

TOML resolution has the same shape with tables in place of objects. It is optional and
has no target here. Mutable resolution, assignment and deletion stay with the default
specification and are open.

## Decision for resolution

`serde_json::Value` and `serde_json::Map` are external. The release traversal calls
`Map::get`, `Vec::len` and slice indexing on them. This specification makes no assumption
about their internals, so no theorem in this profile may be about `serde_json`.

The extractable observation is the release traversal run over a document type defined in
the adapted source. That type needs three cases and nothing else:

- a scalar leaf;
- an array holding a sequence of children, with length and positional access;
- an object mapping decoded key bytes to children, with exact-byte lookup. An association
  list with first-match lookup is acceptable. The theorem must then hold without a
  unique-keys premise, as `lookupKey` does.

The traversal must keep the release loop: split the front token, branch on the node kind,
parse and bound the index or look up the key, then advance `offset` by `1 + tok_len` and
`position` by 1. The theorem relates it to `resolve` through an abstraction from the local
type to `Tree`.

This proves the pointer side of resolution: token splitting, index parsing and bounding,
error choice, and position and offset accounting. It leaves these open, and they must be
reported as open:

- that `serde_json::Map::get` is exact-key lookup in a finite map with unique keys, under
  either map backend;
- that `Value::Array` behaves as the sequence in the model;
- that the adapted traversal equals the release method, which is written directly
  against the external types;
- the borrow relation between the returned reference and the input document.

If the loop over the local type does not extract either, the fallback is a single-step
theorem: one token against one node kind and length gives the right child selector or
error. Report the loop as an extraction blocker in that case. Do not add axioms for
`serde_json`, and do not replace the traversal with the model.

## Adaptation acceptance rules

A faithful adaptation may make these changes, each listed in the profile results:

- Replace `&str`, `String` and `Cow<str>` by the UTF-8 byte slice or a `Vec<u8>`. Theorems
  must not assume UTF-8 validity unless the contract says so; none above does.
- Replace iterators, closures and `str` pattern calls (`bytes().enumerate()`, `position`,
  `find`, `split`, `split_once`, `starts_with`, comparison with a literal) by explicit
  index loops with the same scan order and the same early exits.
- Replace `extend_from_slice` and `push` on a string buffer by pushes on a `Vec<u8>`, in
  the same order.
- Return a reuse flag or an `Option` where the release returns a borrowed `Cow`.
- Replace `unsafe` reference casts and `from_utf8_unchecked` by returning the bytes.
- Replace `str::parse::<usize>` by an explicit checked decimal accumulation. This
  substitutes a standard-library function and must be disclosed as such; see below.
- Define local error and index types that mirror the release variants and fields one for
  one.

It must not change any of these:

- The accepted language of any target.
- The order of checks and so the error precedence, including `NoLeadingSlash` before
  escape errors, `Slash` before `Tilde` after a pending tilde, and `LeadingZeros` before
  `InvalidCharacter`.
- Any offset, position, length or variant in an error payload.
- The points where the release takes a fast path: no first slash or tilde in `Token::new`,
  no tilde in `decoded`, empty input in `validate`.
- Machine arithmetic. Keep `i + 1`, `len + 1`, `offset += 1 + tok_len` and the index
  comparisons as machine operations, so the proof shows they cannot overflow. Do not widen
  types, saturate, or add guards the release lacks. A capacity hint may be dropped only if
  disclosed, since it does not affect the result.
- Panic behaviour. Do not add or remove a bounds check, slice or `expect` that can fail.
- The parts of the release that already extract. Use the release `validate_bytes` and the
  three `Index` bound checks unchanged.

The profile must record the patch against the locked release, check the exact resulting
source bytes before extraction, and leave Aeneas, Charon and the generated Lean unmodified.

## Release correspondence

These obligations are separate from the Lean proofs. Native differential comparison is
evidence for them, not proof.

1. Patch identity: the adapted source is the locked release plus the recorded patch.
2. Body correspondence: each adapted function is named against the release span it
   rewrites, with every substitution from the list above stated.
3. Differential evidence: for each target, compare the adapted function with the release
   API on all byte strings up to a stated length over an alphabet containing at least
   `/ ~ 0 1 2 9 - + a`, a two-byte UTF-8 character, and NUL where the input may be
   arbitrary bytes. Compare complete results, including every error field. State the
   bound and the count. Run both debug and release profiles so overflow checks differ.
4. UTF-8 preservation: `encode` and `decode?` map valid UTF-8 to valid UTF-8. This
   justifies the release's two `from_utf8_unchecked` calls and is not proved here.
5. Standard-library substitution: the checked accumulation agrees with `usize::from_str`
   on nonempty all-digit input, including the `Empty` and `PosOverflow` kinds.
6. Wrappers: generic `Into<Cow<str>>` conversion, `Cow` variants, reference casts, the
   `Tokens` iterator adapter and `Display` are not modelled.
7. External types: everything listed as open under the resolution decision.
8. Target width: theorems are for the 64-bit extraction target.

## Coverage ledger

| API | Required theorem | Profile | Does not establish |
| --- | --- | --- | --- |
| `pointer::validate_bytes` | Outcome on nonempty input at offset zero | default, closed | The empty input; any wrapper |
| `Index::for_len`, `for_len_incl`, `for_len_unchecked` | Bound predicates and exact error fields | default, closed | Index parsing |
| `pointer::validate` | Target 1: outcome equals `pointerError` on every byte slice | adapted | `Pointer::parse`, `PointerBuf::parse`, `from_static`, `FromStr`, `TryFrom`; the string-to-bytes step |
| `Token::new`, `encoded`, `into_encoded` | Target 2: bytes equal `encode x`; reuse condition | adapted | UTF-8 validity of the result; `Cow` variant; `From` conversions |
| `Token::decoded` | Target 3: success everywhere; inverse of `E` on lawful input | adapted | Output on unlawful bytes; UTF-8 validity; `Display` |
| `Token::from_encoded` | Target 4: outcome equals `firstEncError` | adapted | That every other producer of `Token` keeps the invariant; `EncodingError::labels` |
| `Index::from_str`, `Token::to_index`, `is_next`, `TryFrom` | Target 5: outcome equals `parseIndex` | adapted | The `ParseIntError` value; agreement with `usize::from_str`; `ParseIndexError::labels` |
| `Pointer::split_front`, `tokens` | Target 6: first token, remainder, token list | adapted | The `Tokens` adapter; `front`, `back`, `split_back`, `parent`, `get` |
| JSON `Resolve::resolve` | Target 7: outcome equals `resolve` on the local document type | adapted | Anything about `serde_json`; the release method itself; `resolve_mut`; TOML |
| `ResolveMut`, `Assign`, `Delete`, TOML | Tree contracts of the default specification | none | Everything; open |
| Diagnostics, labels, `Report`, miette | Span and classification contracts of the default specification | none | Everything; open, with candidate defects in the notes |
| All other public API | Rows of the default ledger | none | Everything; open |

## Extended scope: every public item

The scope now covers every public item of the release under all features. Sections 8–21
add contracts for the items that targets 1–7 do not cover. Targets 1–7 are unchanged.
[api-inventory.md](api-inventory.md) lists every public item with its contract section or
its exclusion class, and supersedes the last three rows of the ledger above.

The conventions above still apply, with these additions.

- A pointer argument is a byte list satisfying `ValidPointer`, and a token argument is a
  byte list satisfying `ValidEncodedToken`. These are the representation invariants.
  Every operation that returns a pointer or token must also establish the invariant for
  its result. That is part of each contract below, not a separate optional lemma.
- Model functions named below are in the extension part of `SpecModel.lean`.
- Some intended contracts are false for the release. Each is marked **Refuted for the
  release** with the finding that refutes it. The implementer must report such a contract
  as refuted, with the counterexample, and must not weaken it to fit. Proving a separate,
  clearly labelled theorem about what the release does instead is allowed; it is a
  behaviour record, not a contract.
- An excluded item needs a reason from the exclusion classes in the inventory. Difficulty
  is not one of them.

### Tiers

| Tier | Sections | Content |
| --- | --- | --- |
| 0 | default profile | `validate_bytes`, the three `Index` bound checks; closed |
| 1 | 1–7 | Validation wrapper, token codec, index parsing, token splitting, resolution |
| 2 | 8–11 | Pointer navigation, range indexing, byte split, comparison and prefix operations |
| 3 | 12–14 | Buffer construction and mutation, parse wrappers, small token and index items |
| 4 | 15–17 | Mutable resolution, assignment, deletion over the local document type |
| 5 | 18–20 | Error accessors, diagnostic spans, `Report` and `Diagnose` |
| 6 | 21 | Accessors, byte-identity views, equality and order |

Tier 2 depends on target 6. Tier 4 depends on targets 5–7 and on `split_back` from
section 8. Tier 5 contains most of the refuted contracts.

### 8. Pointer navigation (`pointer.rs:120–275`, `token.rs:355`, `component.rs:26`)

Input: a pointer `xs`. All results are in terms of `encodedTokens xs`.

- `count` returns the number of tokens: `count xs`.
- `front` and `first` return the first token, or nothing for the root: `front xs`.
- `back` and `last` return the last token, or nothing for the root: `back xs`.
- `split_back` returns the parent pointer and the last token, or nothing for the root:
  `splitBack xs`. The parent is a valid pointer and `xs = parent ++ "/" ++ token`.
- `parent` returns the first component of `split_back`.
- `get(i)` for a `usize` returns token `i`, or nothing when `i ≥ count`: `getToken xs i`.
  This holds for every `i` up to `usize::MAX`.
- `Tokens::next` yields the tokens in order and then nothing, forever. The observation
  is the full sequence: it equals `encodedTokens xs`. `IntoIterator` for `&Pointer` and
  `&PointerBuf` gives the same iterator.
- `Components::next` yields `Root` first, for every pointer including the root, and then
  each token: `components xs`. `Components::from(&Pointer)` and `Pointer::components`
  build that iterator. `Component::from(Token)` wraps the token.

`"/"` has one empty token and its parent is the root. `"//"` has two empty tokens.

### 9. Range indexing — `Pointer::get` with ranges (`pointer/slice.rs:19–209`)

Input: a pointer `xs` with `n` tokens and a range over token positions. Output: a pointer
made of the selected tokens, or nothing. Every result is a valid pointer and a contiguous
part of `xs`.

| Form | Defined exactly when | Result |
| --- | --- | --- |
| `s..e` | `s ≤ e`, `s < n`, `e ≤ n` | tokens `s` to `e − 1`: `getRange` |
| `s..` | `s < n` | tokens from `s`: `getRangeFrom` |
| `..e` | `e ≤ n` | the first `e` tokens: `getRangeTo` |
| `s..=e` | `s ≤ e`, `e < n` | tokens `s` to `e`: `getRangeIncl` |
| `..=e` | `e < n` | the first `e + 1` tokens: `getRangeToIncl` |
| `..` | always | `xs` |

The start must name an existing token. So `1..1` on a one-token pointer, `0..0` on the
root and `n..` are nothing, while `0..0` on a non-root pointer and `..0` on any pointer are
the root. This differs from slice indexing; the release's own unit tests assert it, so it
is the contract.

`(Bound, Bound)`: an included start `s` is `s`, an excluded start `s` is the natural
number `s + 1`, an included end `e` is `..=e`, an excluded end `e` is `..e`: `getBounds`.
**Refuted for the release** at `Excluded(usize::MAX)` (JSONPTR-002): the contract gives
nothing; the release overflows in the debug profile and selects from token 0 in the
release profile. The contract holds for every other start.

### 10. Byte split — `split_at_offset`, deprecated `split_at` (`pointer.rs:232`, `:253`)

Input: a pointer `xs` and any `usize` offset. Output: `splitAtOffset xs offset`.

The split is defined exactly when byte `offset` of `xs` is a slash. The head is the bytes
before it and the tail starts at it. Both are valid pointers. Offset 0 splits a non-root
pointer into the root and itself; the root has no split. An offset at or past the length,
including `usize::MAX`, gives nothing. `split_at` forwards to `split_at_offset`.

### 11. Comparison and prefix operations (`pointer.rs:278–311`, `:396`)

Input: two pointers. Comparison is on whole tokens.

- `starts_with(other)` holds exactly when `other`'s tokens are a prefix of `self`'s:
  `startsWith`. The root is a prefix of every pointer. `"/ab"` does not start with `"/a"`.
- `ends_with(other)` holds exactly when `other` is not the root and its tokens are a
  suffix of `self`'s, or both are the root: `endsWith`. This is the documented behaviour.
- `strip_suffix(suffix)` returns the leading tokens when `suffix`'s tokens are a suffix of
  `self`'s, and nothing otherwise: `stripSuffix`. The root suffix is accepted for every
  pointer and returns `self`, although `ends_with` rejects it. The result is a valid
  pointer.
- `strip_prefix(prefix)` returns the remaining tokens exactly when `starts_with(prefix)`
  holds, and nothing otherwise: `stripPrefix`. The result is a valid pointer.
  **Refuted for the release** (JSONPTR-001): `"/ab"` minus `"/a"` gives `Some("b")`, which
  is not a valid pointer; the contract gives nothing. The contract holds whenever the
  release returns nothing, and whenever `starts_with` holds.
- `intersection(other)` returns the longest common token prefix, as a prefix of `self`:
  `intersection`. It is the root when the first tokens differ or either side is the root.

### 12. Buffer construction and mutation (`pointer.rs:524–569`, `:921–1056`, `:1116`)

Input: a buffer `xs` and encoded tokens. Output: the final buffer and any returned value.
Every final buffer is a valid pointer. A token argument is first converted with
`Into<Token>`; for a string that is target 2.

- `PointerBuf::new`, `root` and `Default` give the empty buffer.
- `from_tokens(ts)` gives `renderEncoded ts`. `From<Token>` is `from_tokens` of one token.
- `push_back(t)` and `with_trailing_token(t)` give `xs ++ "/" ++ t`: `pushBack`.
- `push_front(t)` and `with_leading_token(t)` give `"/" ++ t ++ xs`: `pushFront`.
- `pop_back` removes and returns the last token, or returns nothing and leaves the root
  unchanged: `popBack`.
- `pop_front` removes and returns the first token, likewise: `popFront`.
- `append(other)` and `concat(other)` give `xs ++ other`: `append`. `append` also returns
  a reference to the buffer.
- `replace(index, t)`: `replaceToken`. When `index < count`, token `index` becomes `t`,
  the other tokens are unchanged, and the old token is returned; the result is always
  `Some`. Otherwise the buffer is unchanged and the error is
  `ReplaceError { index, count }`, with `count = 0` for the root. This holds for every
  `index` up to `usize::MAX`.
- `clear` gives the empty buffer.

`with_trailing_token`, `with_leading_token` and `concat` leave `self` unchanged and return
a new buffer.

### 13. Parse wrappers (`pointer.rs:82`, `:104`, `:942`, `:1059`, `:1122`, `:1144`)

Each wrapper has the outcome of target 1 on the UTF-8 bytes of its argument.

- `Pointer::parse`, `PointerBuf::try_from(&str)`, `PointerBuf::try_from(String)` and
  `PointerBuf::from_str` succeed with a pointer whose bytes are the input, or fail with
  the `ParseError` of target 1.
- `PointerBuf::parse` succeeds likewise, or fails with a report whose original error is
  that `ParseError` and whose subject is the unchanged input.
- `Pointer::from_static` returns a pointer whose bytes are the input when the input is
  valid. On invalid input it panics, as documented. Its theorem is therefore: success
  exactly when `pointerError` is `none`. This is the one contract here that is not total.

What a theorem about an adapted wrapper adds over target 1 is the result bytes and the
report fields. The reference casts stay excluded; see the inventory.

### 14. Small token and index items (`token.rs:169–331`, `index.rs:157–229`, `:417`)

- `Token::encoded` and `into_encoded` return the encoded bytes held by the token.
- `Token::into_owned` and `to_owned` return a token with the same encoded bytes.
- `Token::from(&str)`, `from(&String)` and `from(String)` are `Token::new` (target 2).
- `Token::from(&Token)` and `Clone` return a token with the same encoded bytes.
- `Token::is_next` holds exactly when the encoded bytes are `-`: `isNext`.
- `Index::from(usize)` returns `Num` of the argument.
- `Index::try_from` for `&str`, `String`, `&String`, `&Token` and `Token` is target 5 on
  the string, or on the token's encoded bytes.
- `InvalidCharacterError::offset` returns the stored offset.
- `StringOrToken::from(String)`, `from(Token)` and `deref`: the dereferenced bytes are the
  string, or the token's encoded bytes.

### 15. Mutable resolution — `ResolveMut::resolve_mut` (`resolve.rs:325`, `:425`)

Input: a document and a pointer. Output: a mutable reference to the selected node, or a
`resolve::Error`. The observation is over the local document type of target 7.

Contract:

- The outcome, as a value or an error, equals that of target 7 for the same arguments.
- On success, writing a node `new` through the returned reference leaves the document
  equal to `replaceAt usize::MAX root keys new`. Nodes off the path are unchanged.
  Writing back the node that was read leaves the document unchanged.
- On error the document is unchanged.

In Aeneas terms the forward result is the node and the backward function is `replaceAt`.
JSON and TOML have separate release bodies with the same shape.

### 16. Assignment — `Assign::assign` (`assign.rs:267–428`, `:439–598`)

Input: a document, a pointer and a value. Output: the replaced value if any, or an
`assign::Error`; and the final document.

Contract: the outcome and the final document equal `assign usize::MAX root keys v`.

- No tokens left: the node becomes `v` and the old node is returned. The empty pointer
  replaces the whole document.
- At an array: parse the encoded token as in target 5; an error gives
  `FailedToParseIndex`. Apply the inclusive bound; failure gives `OutOfBounds`. An index
  below the length continues at that item. An index equal to the length, numeric or `-`,
  appends the expansion of the remaining tokens and returns nothing.
- At an object: a present key continues at its value. An absent key adds a member holding
  the expansion of the remaining tokens and returns nothing.
- At a scalar with tokens left: the scalar becomes the expansion of all remaining tokens,
  the current one included, and the old scalar is returned.
- Expansion (`expand`) wraps the value once per remaining token, outermost first. A token
  spelled `0` or `-` makes a one-item array. Any other token, including `1`, makes a
  one-member object keyed by the decoded token.
- Errors carry `position` and `offset` as in target 7. On error the document is unchanged.
- When the pointer resolves, assignment returns the resolved node and the final document
  is the write-back of section 15 (`assign_existing`).

A new object member goes at the end of the member list in the model. The local document
type must do the same, so that theorems are exact equalities. Member order in
`serde_json` and `toml` maps is theirs and is outside this contract.

Assignment does not always make the pointer resolvable afterwards: after assigning at
`/a/-`, the token `-` still fails to resolve. That is the documented expansion rule, not
a finding.

### 17. Deletion — `Delete::delete` (`delete.rs:96`, `:134`)

Input: a document and a pointer. Output: the removed value if any; and the final document.

Contract: both equal `delete usize::MAX rootRepl root keys`.

- Empty pointer: the document becomes `rootRepl` and the old document is returned.
  `rootRepl` is JSON null, or an empty TOML table.
- Otherwise resolve the parent pointer. At an array, a token that parses and passes the
  strict bound removes that item; later items keep their order. At an object, a present
  decoded key removes that member; the other members are unchanged.
- Every other case returns nothing and leaves the document unchanged: the parent does not
  resolve, the parent is a scalar, the token is not a valid index or is `-` or is out of
  bounds, or the key is absent.
- A value is returned exactly when a non-root pointer resolves, and it is the resolved
  node (`delete_some_iff`).

Removal from the model's member list removes the first entry for the key and keeps the
order of the rest. Order after removal in an external map is outside this contract.

### 18. Error accessors (`pointer.rs:1189–1320`, `resolve.rs:168–209`, `assign.rs:163–191`)

Each accessor is a total function of the error value.

- `ParseError::offset` and `pointer_offset` return 0 for `NoLeadingSlash` and the pointer
  offset `d` for `InvalidEncoding`. `source_offset` returns 0 or the source offset `t`.
- `is_no_leading_slash`, deprecated `is_no_leading_backslash` and `is_invalid_encoding`
  hold exactly for their variant.
- `resolve::Error` and `assign::Error`: `offset` and `position` return the stored fields
  for every variant. Each `is_*` holds exactly for its variant.
- `ParseError::complete_offset` returns `d + t`, the position of the offending tilde, or 0.
  The contract covers every error value with `d + t ≤ usize::MAX`, which includes every
  error the parser produces. Total success for all field values is **refuted for the
  release** (N7): the variant is publicly constructible and the addition overflows.

### 19. Diagnostic spans (`pointer.rs:1196–1227`, `token.rs:415–434`, `index.rs:358–391`, `resolve.rs:212–236`, `assign.rs:211–236`, `diagnostic.rs:37`)

A label is a text, a byte offset and a byte length in the subject. The observation is
whether a label is produced, its offset and its length. Label texts built with
`to_string` or `format!` are excluded; fixed texts may be checked as a variant tag.
`Label::new` stores its three arguments.

- `ParseError::invalid_encoding_len(subject)`, for an error produced by parsing `subject`:
  0 for `NoLeadingSlash`; otherwise 2 when a byte follows the offending tilde and 1 when
  the tilde is the last byte: `invalidEncodingLen`. The span then lies inside the subject.
  **Refuted for the release** (JSONPTR-003): `"/~"` gives 2. Total success for an
  arbitrary subject is also refuted (N5): the empty subject underflows.
- `ParseError::labels(subject)`: one label at `complete_offset` with that length:
  `ptrErrLabel`. Refuted wherever the length is.
- `EncodingError::labels(subject)`: one label of length 1: `encErrLabel`. A `Slash` error
  is labelled at its offset. A `Tilde` error is labelled at its offset, or one byte
  earlier when the offset equals the subject length. For an error produced by
  `from_encoded` on `subject` the span lies inside the subject. The contract covers
  errors with offset at least 1 when the source is `Tilde`. Total success for all field
  values is **refuted for the release** (N8).
- `ParseIndexError::labels(subject)`, for an error produced by parsing `subject`:
  `IndexErrLabelPost`. `InvalidInteger` has no label. `LeadingZeros` is labelled from
  offset 0 over the leading zeros, and must not panic when the subject is all zeros.
  `InvalidCharacter` is labelled from its offset over the bytes up to the next ASCII digit
  or the end. **Refuted for the release**: an all-zero subject panics (N1); the
  `InvalidCharacter` length is wrong whenever no digit follows or a multibyte character
  is in the run (N2).
- `resolve::Error::labels(origin)` and `assign::Error::labels(origin)`: `tokenErrLabel`.
  No label when `origin` has no token at the error's position. Otherwise the length is
  the token's encoded length, and the offset is one past the error offset, or the error
  offset itself when that separator is the last byte of `origin`. The contract covers
  errors with `offset < usize::MAX`. Total success for all field values is **refuted for
  the release** (N6).
- `Diagnostic::url()` returns the docs.rs address of the error type for this crate
  version. **Refuted for the release** for `resolve::Error` (N3), which returns the
  address of `assign::Error`.

### 20. Reports — `Report`, `Diagnostic::into_report`, `Diagnose` (`diagnostic.rs:13`, `:66–97`, `:207–227`)

A report is a pair of an error and a subject.

- `into_report(subject)` builds the pair from the error and the converted subject.
- `subject`, `original`, `decompose`, `into_original` and `deref` return the stored
  components unchanged.
- `Result::diagnose(subject)` maps `Ok(t)` to `Ok(t)` and `Err(e)` to the report of `e`
  and the converted subject.
- `Result::diagnose_with(f)` does the same with the subject `f()`. It calls `f` exactly
  once on `Err` and never on `Ok`.

These are generic over the error type. A theorem may be stated for each of the crate's
five `Diagnostic` implementations, or once under an explicit premise on the trait
instance.

### 21. Accessors, views, equality and order

- `Pointer::is_root` and `is_empty` hold exactly for the empty pointer. `len` returns the
  byte length. `to_buf`, `ToOwned::to_owned` and `Clone` for `PointerBuf` return the same
  bytes in a new buffer.
- Views return the same bytes: `as_str`, `AsRef<str>`, `AsRef<[u8]>`, `Borrow<str>`,
  `PointerBuf::as_ptr`, `AsRef<Pointer>`, `Borrow<Pointer>`, the two `Cow` conversions.
  `Default for &Pointer` is the root.
- Equality between any two of `Pointer`, `&Pointer`, `PointerBuf`, `str`, `&str` and
  `String`, in every implemented direction, holds exactly when the two byte lists are
  equal. `Token` equality compares encoded bytes. `Component`, `Index` and the error
  types compare structurally.
- Order between the same pairs is lexicographic on bytes: `bytesLt`. It is not a
  token-wise order: `"/a-"` sorts before `"/a/b"`. `Token` order is lexicographic on
  encoded bytes. `Index` orders `Num` by value and puts every `Num` before `Next`.
  `Component` puts `Root` before every token.
- `Clone` and `Copy` on the plain-data types return an equal value.

Derived implementations on plain-data types (`Index`, `InvalidEncoding`, the error
structs and enums) have compiler-generated bodies that may extract from the release
unchanged; prefer that to an adaptation. Comparisons on string-backed types delegate to
the standard library's `str` comparison, so an adapted theorem substitutes a byte loop
for it and must say so.

## Adaptation rules for the extended scope

The rules above apply. These are added.

- The local document type of target 7 serves sections 15–17. Add only the operations the
  release uses: positional replace, append and remove on arrays; lookup, replace, insert
  at the end and remove on objects.
- Model `mem::replace` on a `&mut` node as the write-back it is. Do not copy the document.
- Keep the release order of effects in assignment: no mutation before the index of the
  current array token has parsed and passed its bound.
- `Box<dyn Iterator<Item = Label>>` becomes an optional label. A text built by formatting
  becomes a variant tag.
- An iterator type (`Tokens`, `Components`) becomes its remaining input plus the state
  the release keeps, with `next` as a function on that state.
- A generic `impl Into<Token>` parameter becomes an encoded token; the conversion is
  target 2 and is composed in the theorem statement.
- The JSON and TOML bodies are separate release spans. One adapted function may stand for
  both only if the patch record maps it to both spans and states the one difference
  (the root replacement on delete).

Correspondence obligations added: member order and removal order in external maps; the
`preserve_order` feature of `serde_json`, which this crate does not select; every
formatted text; every reference and `Box` cast; hashing.
