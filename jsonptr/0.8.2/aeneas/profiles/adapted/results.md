# jsonptr 0.8.2 adapted profile: status

Current managed run: `.work/runs/adapted-evibwt5j` (2026-11-28) passed on
`aarch64-apple-darwin`, with identical before/after input fingerprints, exact
regeneration of the adapted model, patch-identity checks, both differential
harnesses, and the audit of 92 theorems (67 contract theorems, 25 support
theorems including checked refutations). The default run `default-lhpdidha`
used the same version-root inputs. The command was
`AENEAS_LAKE_CACHE=<default build>/.lake/packages bash scripts/verify.sh --profile adapted --offline`.
Targets 1–7 below were first established in run `adapted-1purn8wf`; tiers 2–6
are described in [Tiers 2–6](#tiers-26-specification-sections-821).

Every theorem below is about an **adapted** function, a byte-slice rewrite of a release
body produced by the recorded patch. None of them is a theorem about the release API.
`proofs.toml` maps no public API. The release-correspondence obligations in
[specification.md](specification.md#release-correspondence) are not checked by Lean.

## Formally checked

The audit checks each theorem's kind and its transitive axioms. Only `propext`,
`Classical.choice` and `Quot.sound` are allowed, and the audit finds no `sorry`, custom
axiom or native decision. Each contract is total success: the generated body returns
Aeneas `ok`, carrying the exact Rust value or Rust error that the contract names.

| Target | Theorem (module) | Proposition in `proofs/Specs.lean` | Premise |
| --- | --- | --- | --- |
| 1 `pointer::validate` | `validateAdapted` (`Proofs.Validate`) | `ValidateContract`: the outcome is `pointerError xs`, and success returns the input | none |
| 2 `Token::new` / `encoded` | `newAdapted` (`Proofs.Codec`) | `EncodeContract`: the bytes are `encode x`, and the input is reused exactly when `needsNoEncoding x` | `len ≤ isize::MAX` |
| 3 `Token::decoded` | `decodedAdapted` (`Proofs.Codec`) | `DecodeContract`: total. On lawful input the output is the unique `x` with `encode x = e`. The input is reused exactly when it has no `~` | `len ≤ isize::MAX` |
| 4 `Token::from_encoded` | `fromEncodedAdapted` (`Proofs.Token`) | `FromEncodedContract`: the outcome is `firstEncError e`, and success returns the input | none |
| 5 `Index::from_str` / `to_index` | `fromStrAdapted` (`Proofs.Index`) | `IndexContract`: the outcome is `parseIndex usize::MAX s` | none |
| 6 `Pointer::split_front` / `tokens` | `splitFrontAdapted` (`Proofs.Split`) | `SplitFrontContract`: the first token and remainder, with no byte lost and the token list preserved | empty input, or first byte `/` |
| 7 JSON `Resolve::resolve` | `resolveAdapted` (`Proofs.Resolve`) | `ResolveContract`: the outcome is `resolve usize::MAX (toTree doc) keys`, with the exact node or error, position and offset | `render keys = bytes ptr`, `len ≤ isize::MAX` |

The audit also checks these support theorems:

- `resolveStepAdapted` (`ResolveStepContract`): one loop iteration.
- The specification's sanity facts `forLen_ok_lt`, `Model.decode_encode`,
  `Model.encode_injective` and `Model.encode_length`.

How the proofs reach the contracts:

- **Target 1:** the proof shows that the release `validate_bytes` computes the model's
  executable scan `ptrScan`. That scan is `pointerError`. The sanity facts
  `pointerError_post` and `PointerPost_unique` are not used, and they are not proved
  here.
- **Target 7:** the proof is by induction on the keys, through `resolve_rec_adapted` at
  arbitrary position and offset. The helper assumes that those values plus the remaining
  pointer length fit in `usize`. The mapped theorem has no such premise, because it starts
  from 0 and the slice bound gives the rest.

`proofs/SpecModel.lean` copies the target 1–7 part of the specification agent's model
word for word. The proofs never rely on the draft's unproved sanity theorems.

## Extraction

Every core target was first probed on its unchanged release body. Every probe was blocked
by an unsupported string, iterator or `serde_json` construct, so no release body is
proved. The probe logs are in the ignored `.work/sol/probes/`.

All adapted entry points are generated into one model,
`proofs/Generated/aarch64-apple-darwin/JsonptrAdapted.lean`. It uses the default
profile's Charon options. It contains no axiom, opaque or `sorry`, and it regenerates byte
for byte.

**Extraction blocker:** the loop form `resolve_adapted` does not extract. A loop that
reassigns a shared borrow to a child of its own pointee causes an Aeneas internal error.
This happens with `Vec` children and with `Box` children. The primary approved a
tail-recursive replacement.

## Adaptation and disclosures

[`patches/adapted-bodies.patch`](patches/adapted-bodies.patch) only adds code. Every
release item stays byte-identical. [`scripts/prepare-source.py`](scripts/prepare-source.py)
applies the patches to a fresh copy of the locked release and checks every resulting file
against [`adapted-source.json`](adapted-source.json).

| Adapted function | Release span | Substitutions |
| --- | --- | --- |
| `pointer::validate_adapted` | `pointer.rs:1355` | Byte slice instead of `&str`. The release `validate_bytes` is called unchanged. |
| `token::from_encoded_adapted`, `from_encoded_scan_adapted` | `token.rs:77-111` | Index loop instead of `bytes().enumerate()`. The loop is moved into a helper that returns `()`, and the wrapper returns the input. |
| `token::new_adapted`, `position_slash_or_tilde_adapted` | `token.rs:128-163` | Index loops instead of `position` and the `for` loop. Two pushes per escape. `None` for the reused `Cow`. The bytes instead of `from_utf8_unchecked`. `with_capacity(len + 1)` and `extend_from_slice(&input[..i])` are kept. |
| `token::decoded_adapted`, `position_tilde_adapted` | `token.rs:224-262` | As for `new_adapted`. `i + 1` and the escape state machine are kept. |
| `index::from_str_adapted`, `position_non_digit_adapted` | `index.rs:166-189` | Byte tests. A byte-position loop that calls the included standard-library body of `u8::is_ascii_digit`. A `match` instead of `map_or_else`. Local error types that carry the error kind only. |
| `index::parse_usize_digits_adapted` | replaces `str::parse::<usize>` | A standard-library substitution, not release code. It is checked decimal accumulation with `checked_mul` and `checked_add`, returning the `Empty` and `PosOverflow` kinds. It is partial on its own: `s[i] - b'0'` underflows below 48. Its precondition is that every byte is an ASCII digit, and `from_str_adapted` calls it only after that check. |
| `pointer::split_front_adapted`, `find_slash_adapted` | `pointer.rs:181-207` | Index loop instead of `find('/')`. An empty slice instead of `Self::root()`. `&s[1..]` and `split_at` are kept. |
| `resolve::resolve_step_adapted` | `resolve.rs:290-313` | The loop body over the local document type. `from_str_adapted` on the encoded token, then the release `for_len` and `&v[idx]`. On objects, `lookup_adapted` on the bytes from `decoded_adapted`. A `match` instead of `map_err` and `?`. |
| `resolve::resolve_rec_adapted`, `resolve_recursive_adapted` | `resolve.rs:287-317` | **Tail recursion replaces the loop.** The token order, the early exit on error and the machine operations `offset + (1 + tok_len)` and `position + 1` are kept. Native recursion depth equals the token count, so a very long pointer can overflow the stack where the release loop cannot. Stack depth is outside the Aeneas model and is a correspondence obligation. |
| `resolve::resolve_adapted` | `resolve.rs:283-318` | The loop form, kept in the patch but not extracted. Its agreement with the recursive form rests on inspection and the differential evidence only. |

The resolution decision requires new code that is not release code: `DocAdapted`,
`ResolveErrorAdapted`, `lookup_adapted` (first-match lookup) and `bytes_eq_adapted`. No
theorem says anything about `serde_json`. Still open:

- that `Map::get` is exact-key lookup with unique keys;
- that `Value::Array` behaves as the modelled sequence;
- that the adapted traversal equals the release method;
- the borrow relation of the returned reference.

[`patches/cargo-workspace.patch`](patches/cargo-workspace.patch) adds `[workspace]` and a
`[[patch.unused]] creusot-std` lock entry. The entry accommodates the repository's
untracked ancestor `.cargo/config.toml` under the managed runner's `--locked` cargo
invocation. It does not change the resolved dependency graph. The differential harness
lock carries the same entry.

## Native differential evidence

This is not proof. In the same run, [`differential/`](differential) compared the release
APIs with the adapted functions inside the patched tree, in both debug and release builds.

- **Inputs:** every string of at most 7 characters over `/ ~ 0 1 2 9 - + a NUL é`, which
  is 21,435,888 strings. Also 20,140 decimal strings near `usize::MAX` and powers of ten,
  each plain and with a leading `0`, a leading `+`, a trailing `a` or a trailing `é`.
- **What is compared:** complete results, every error field, and input reuse.
- **`decoded`:** only on lawful tokens, because the public API cannot build an unlawful
  one.
- **Resolution:** four documents. The release `serde_json` method is compared with the
  adapted loop, with repeated step calls and with the recursive form.

Every comparison agreed.

## Open

- Equivalence of each adapted body to the release body, and of `resolve_recursive_adapted`
  to the loop. Each is a reviewed argument plus differential evidence.
- UTF-8 preservation by `encode` and `decode?`.
- The standard-library substitution against `usize::from_str`.
- The `serde_json` facts listed above.
- Stack depth of the recursive form.
- `Cow` conversions and the `Tokens` iterator adapter themselves (their logic is
  covered by adapted bodies, not the adapter types).
- `EncodingErrorLabelContract` (needs the model lemma `firstEncError_offset_le`) and
  the statement-only `InvalidEncodingLenReleaseRecord`.
- Member and removal order inside the external `serde_json`/`toml` maps.

## Tiers 2–6 (specification sections 8–21)

A second add-only patch, [`patches/adapted-api.patch`](patches/adapted-api.patch),
adds `src/adapted_api.rs`; target 1–7 declarations in the generated model are
byte-identical to before. Every row of [api-inventory.md](api-inventory.md) is
either covered here, in the default profile, or excluded with a reason below.
All theorems are about adapted functions; no public API is mapped.

| Tier | Closed contracts | Checked refutations (finding) |
| --- | --- | --- |
| 2 navigation, ranges, prefix/suffix | tokens, count, front, back, split_back, parent, `get(usize)`, components, `Component::from`, six range forms, split_at_offset, starts_with, ends_with, strip_suffix, intersection | `stripPrefix_refuted` (JSONPTR-001), `getBounds_refuted` at `Excluded(usize::MAX)` (JSONPTR-002) |
| 3 buffers and parse wrappers | `PointerBuf::new`, to_buf, from_tokens, push_back, push_front, pop_back, pop_front, append, replace, clear, with_leading/trailing_token, concat, token encoded/to_owned, `StringOrToken`; `Pointer::parse`, `PointerBuf::parse`/`try_from` ×2, `from_static` (fails with `.assertionFailure` on malformed input), `is_next` — the last six discharged against `validateAdapted`/`fromStrAdapted` | — |
| 4 mutation | `ResolveMut` (outcome, write-back, unchanged on error), `Assign`, `Delete` for JSON and TOML: exact final documents | — |
| 5 errors and diagnostics | `resolve::Error` and `assign::Error` accessors; resolve/assign labels for `offset < usize::MAX`; `diagnose` over `Result<usize, ParseError>` | JSONPTR-003 (`invalidEncodingLen_refuted`, `parseErrorLabel_refuted`), JSONPTR-004/N1 (`parseIndexErrorLabel_refuted`), JSONPTR-005/N2 `"1abc"` (`parseIndexErrorLabel_refuted_N2`), JSONPTR-008 (`invalidEncodingLenTotal_refuted`, `encodingErrorLabelTotal_refuted`, `resolveErrorLabelTotal_refuted`, `assignErrorLabelTotal_refuted`) |
| 6 accessors, equality, order | is_root, is_empty, len, all equality directions, Token and Component equality, byte order with `partial_cmp = Some cmp`, Component order, `PointerBuf` clone | — |

JSONPTR-005's character-versus-byte case (`"aé1"`) and JSONPTR-007 (a
documentation mismatch) have native evidence only.

**Premises** beyond the representation invariants (`ValidPtr`, `ValidTok`,
`render keys = bytes ptr`): `LenBound` on built buffers and `TreeBound` (every
input array/object has fewer than `usize::MAX` entries) in `AssignContract`.
Both are input-representability premises: a real `Vec` of a non-zero-sized type
cannot reach `usize::MAX` entries; they are needed because the Aeneas `Vec`
model fails at full length.

**Disclosed substitutions** (all accepted by the specification agent): token
length read at yield time in range/zip loops; `nth` as an explicit
`advance_by` loop; `push_front` rebuilt as push plus two extends (the Aeneas
`Vec::insert` model fails at `index == len`); `split_off`, `pop`, `remove(0)`,
`mem::replace`/`take`, `clear`, `Vec::remove` and `Map::remove` replaced by
rebuilt buffers with equal final contents; `replace` collecting owned copies;
`from_tokens` over `&[Vec<u8>]`; `Component` eq/cmp by value; a local `Bound`
mirror; a byte loop for `[u8]::cmp`; first-match key search for
`get_mut`/`entry`/`remove`, vacant entries appended; tail recursion for the
mutation traversals (stack depth as for target 7); one adapted function for
both the JSON and TOML `resolve_mut` and `assign` bodies, mapped in
[`adapted-source.json`](adapted-source.json) to `resolve.rs:325` and `:425`
and `assign.rs:267–428` and `:439–598`; `delete` takes the root replacement
as a parameter. `Leaf 0` stands for JSON null by convention; scalar payloads
are otherwise uninterpreted. JSONPTR-001 and JSONPTR-002 arithmetic is
preserved, not fixed.

**Dropped char-boundary assertions.** The release's `str` slicing asserts a
char boundary at several call sites that the byte-level rewrites do not
repeat. Each has an audited support theorem showing the standard-library
condition holds there: `splitAtOffset_charBoundary` (no premise),
`popFront_generated_charBoundary`, `popBack_generated_charBoundary`
(`ValidUtf8`), and `sliceOne_generated_charBoundary` (`&s[1..]` in
`split_front`, `front` and `pop_front`; `ValidPointer`, `ValidUtf8`), all
stated over the generated functions. `pushFront_charBoundary` is stated over
the input buffer, because the rebuilt body has no `insert` call to attach it
to. `ValidUtf8` is a byte-level RFC 3629 definition used only in these lemmas.

**Not expressible with the unchanged tools.** The generated `Diagnostic`
trait structure fails Lean universe inference ("Failed to infer universe
levels in type of field `labels`"), so generic `Report::subject`, `Deref`,
`into_report`, `diagnose` and `diagnose_with` are excluded. `Display`/`Debug`
and `to_string` are excluded because the backend `Formatter` model returns the
formatter unchanged and no output text is observable; `Error::source` because
`dyn Error` needs axioms for `Display`, `Debug` and the `source` default. Both
exclusions were probed, not assumed. Hashing, raw-pointer/`Box` casts, trait
declarations and serde/serde_json/toml/miette behaviour are excluded as in the
inventory.

**Differential evidence (not proof).** In the same run,
[`differential-api/`](differential-api) made 174,407,215 comparisons in each of
debug and release with no disagreement: every string up to 6 characters over
the same alphabet, pointer pairs, token lists, boundary indices and every
`Bound` pair, hand-built error values, final buffers for every mutation, and
377,740 `resolve_mut`/`assign`/`delete` cases against the release `serde_json`
methods (members sorted; external map order is outside the contract). TOML
was not exercised natively.
