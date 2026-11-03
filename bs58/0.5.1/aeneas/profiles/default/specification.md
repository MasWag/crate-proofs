# Specifications for bs58 0.5.1

Target: upstream tag `0.5.1`, commit
`7d3c9282d2595612e5474df93dd0e017db9b684f`. This document describes
contracts derived from the unchanged `src/` implementation. It is a specification
and findings document, **not evidence that every listed property has been proved**.
The proof inventory must identify which numbered obligations are actually proved
about unmodified-Aeneas-generated definitions. Tests and independently implemented
models do not establish those obligations by themselves.

## 1. Mathematical definitions

A byte sequence is a finite list of natural numbers less than 256. Define
`value_b([d_0,...,d_(k-1)]) = Σ_i d_i * b^(k-1-i)`.
Let `digits_b(n)` be the unique big-endian base-b expansion with no leading zero,
using the empty sequence when `n = 0`. Let `lz(x)` count leading zero bytes.

A valid alphabet `A` consists of 58 distinct ASCII bytes `a[0..58)` and a
128-entry inverse table `t` such that, for every `c < 128`,
`t[c] = i` if `a[i] = c`, and `t[c] = 255` if there is no such index.
No restriction to printable ASCII is intended: NUL and other control bytes are
permitted by `Alphabet::new`.

For any byte sequence `x`, define
`E_A(x) = repeat(a[0], lz(x)) ++ map(a, digits_58(value_256(x)))`.
For a sequence `s` consisting solely of alphabet bytes, define
`D_A(s) = repeat(0, leading_count(a[0], s)) ++ digits_256(value_58(map(t,s)))`.
These definitions fix empty-input, all-zero-input, leading-zero, byte-order, and
canonical-representation behavior without referring to the implementation.

## 2. Alphabet construction obligations

**A1 — complete success characterization.** For every `[u8;58]` input `a`,
`Alphabet::new(a)` returns `Ok A` if and only if all bytes are ASCII and pairwise
distinct. On success, `A.encode = a` and the inverse-table definition above holds
for every `c < 128`. The function terminates without panic for every such input,
including invalid inputs. Do not require alphabet validity as a precondition for
this entire theorem: invalid-input behavior is part of the result.

**A2 — exact failure selection.** Let `j` be the least index such that
`a[j] ≥ 128` or there exists `i < j` with `a[i] = a[j]`. If `a[j] ≥ 128`, the result
is `NonAsciiCharacter {index:j}`. Otherwise the result is
`DuplicateCharacter {character:char(a[j]), first:i, second:j}`, where `i` is the
unique matching earlier index (the prefix before `j` is valid). Errors at later
indices must not take precedence. A1 and A2 together are a total contract.

**A3 — inverse laws.** For every successful constructor result and `i < 58`,
`A.decode[A.encode[i]] = i`; for every `c < 128` with `A.decode[c] < 58`,
`A.encode[A.decode[c]] = c`. The distinguished sentinel 255 cannot be a valid
digit. Prove these as corollaries of construction, not assumptions about arbitrary
internal tables.

**A4 — unwrap and constants.** `new_unwrap` returns the same alphabet as `new`
on valid input and panics on invalid input. All named built-ins are valid;
`DEFAULT = BITCOIN` and `MONERO` has the same alphabet bytes as `BITCOIN`.
The latter says nothing about implementing Monero's block-based address codec.

Useful constructor loop invariant at position `i`: `i ≤ 58`; the processed
prefix is ASCII/injective; `encode[j]=a[j]` for `j<i`; and for every ASCII byte,
`decode[c]` is its unique index in that prefix or 255. The invariant must describe
unprocessed table entries as well as entries already set.

## 3. Unchecked core codec obligations

These obligations assume a valid alphabet. The generic private encoder additionally
needs its cloned and original iterators to enumerate the same finite byte sequence;
the public slice and checksum-chain call sites have this property. Rust's `Clone`
trait alone does not promise it for arbitrary user-defined iterators.

**E1 — encoding with arbitrary initial output.** For every input `x` and mutable
byte buffer initially equal to `o` of length `m`, unchecked encoding succeeds if
and only if `|E_A(x)| ≤ m`. On success it returns exactly `|E_A(x)|`, writes
`E_A(x)` into the corresponding prefix, and preserves `o[|E_A(x)|..m)` exactly.
Otherwise it returns `BufferTooSmall`. There is no transactional/unchanged-buffer
promise on error. A total-correctness theorem must include all finite inputs, not
only inputs of a fixed test size.

**D1 — decoding valid strings.** For every alphabet-only input `s` and initial
byte buffer `o` of length `m`, unchecked decoding succeeds iff `|D_A(s)| ≤ m`.
On success it returns that exact length, writes `D_A(s)` as the prefix, and
preserves the remaining suffix. Otherwise it returns `BufferTooSmall`.

**D2 — invalid input and error precedence.** Let `j` be the first byte not in the
alphabet and let `p=s[0..j)`. If
`|digits_256(value_58(map(t,p)))| ≤ m`, the error is `NonAsciiCharacter {index:j}`
when `s[j] ≥ 128`, and `InvalidCharacter {character:char(s[j]),index:j}` otherwise.
If this numeric-prefix size exceeds `m`, `BufferTooSmall` occurs before reaching
`j`. Leading zero symbols are appended only after validation of the entire input,
so they are **not** included in this prefix-capacity condition. For example,
`"10"` with the Bitcoin alphabet and a zero-length output reports invalid `'0'`
at index 1, whereas `"20"` with a zero-length output reports `BufferTooSmall`.

**D3 — const decoder.** With `Check::Disabled`, for all `N`, valid `A`, and valid
`s`, `into_array_const::<N>()` succeeds iff `|D_A(s)| ≤ N`; its result is
`D_A(s) ++ repeat(0, N - |D_A(s)|)`. It does not enforce exact decoded length and
does not left-pad. For invalid inputs the D2 error-selection rule applies with
`m=N`. A checksum-enabled builder passed to this API panics at its explicit
assertion; checksum support must not be silently presumed.

**R1 — two-sided round trips.** For all byte sequences `x`, `D_A(E_A(x)) = x`.
For all alphabet-only sequences `s`, `E_A(D_A(s)) = s`. These imply injectivity
of both transforms on their respective domains, including leading zeros. To
claim an implementation round trip, compose E1 and D1 about extracted code with
these mathematical identities and prove the required capacity conditions.

**B1 — bounds and machine arithmetic.** For `n=|x|`,
`|E_A(x)| ≤ n + ceil(n/2)` and, for valid `s`, `|D_A(s)| ≤ |s|`.
The encoder's `max_encoded_len(n)` equals `n + ceil(n/2)` provided both source
additions fit `usize`. An explicit sufficient precondition is
`n + ceil(n/2) ≤ usize::MAX` over mathematical naturals. There is no unconditional
no-overflow claim for arbitrary `usize`: the actual expression is
`n + (n + 1)/2`. Allocating targets additionally require `original_len + max_len`
to fit and allocation success. These are resource/arithmetic preconditions, not
alphabet assumptions.

Arithmetic proof facts: encoder carry starts at most 255; each digit step has
`carry + digit*256 ≤ 255 + 57*256 = 14847`, and the next carry is at most 255.
Decoder carry starts at most 57; each byte step has
`carry + byte*58 ≤ 57 + 255*58 = 14847`, and the next carry is at most 57.
Thus these arithmetic steps fit even 16-bit `usize`. Numeric digits are kept
little-endian internally and reversed on success. An adequate loop invariant
relates the active output prefix to the mathematical value of the consumed input,
states `index ≤ output.len()`, and preserves the inactive suffix. The size bound
can use `256^2 < 58^3` and `256 < 58^2` rather than floating-point logarithms.

## 4. Public wrapper and target obligations

**W1 — builders.** Universally quantify input and alphabet when proving `new`,
`from_input`, and `with_alphabet`: preserve input, set the requested/default
alphabet, and initialize/preserve the checksum mode exactly as the source does.
Analogous setter properties apply to checksum and version selections.

**W2 — growable targets.** On success `Vec`, `SmallVec`, `TinyVec`, and `String`
append the computed output to the original contents and return the appended
length. Fixed targets overwrite from the beginning. `ArrayVec`/`SliceVec` append
within spare capacity and can return `BufferTooSmall`. These claims assume their
respective dependencies' standard target behavior and sufficient machine/allocation
resources; they are outside a no-default-features proof unless separately extracted.
For `DecodeTarget::decode_with` on `Vec`, an error leaves the resized vector in
place because `?` skips `truncate`; no rollback guarantee is documented.

**W3 — mutable strings.** On success `&mut str` receives ASCII output in its
prefix; if that prefix splits an old UTF-8 codepoint, its remaining continuation
bytes (at most three) are replaced by NUL. UTF-8 validity is restored by the
guard, including on unwinding. This unsafe adapter, `Drop`, and UTF-8 library
semantics need a separate memory/safety argument; a proof of the arithmetic core
does not cover them. The public trait callback may write arbitrary bytes, making
the guard's full validity guarantee stronger than just the normal encoder case.

## 5. Checksum modes: intended contracts and actual findings

Let `P` be input bytes optionally prefixed by the requested version byte.
Base58Check computes `C(P)=first4(SHA256(SHA256(P)))`; CB58 computes
`C(P)=last4(SHA256(P))`. Encoding should produce `E_A(P ++ C(P))`.
Decoding first applies unchecked decoding, requires at least four decoded bytes,
verifies the checksum, and returns `P`, **including** a version byte if present.
When a version is requested, intended acceptance requires `|P| ≥ 1` and
`P[0] = requested_version`. SHA-256 functional correctness is a distinct proof
obligation; treating it as an uninterpreted function proves only composition.

The following are reproduced against the unchanged local source with both
`check` and `cb58`. They must be reported as findings rather than repaired in the
target or hidden by strengthening preconditions without disclosure.

**F1 — empty payload accepted as versioned data.** For checksum-only data, the
implementation compares `output[0]` (the first checksum byte) to the requested
version instead of requiring a nonempty payload. Base58Check input `"3QJmnh"`
with `with_check(Some(93))` returns `Ok([])`. CB58 input `"45PJLL"` with
`as_cb58(Some(120))` likewise returns `Ok([])`. Both are valid encodings of empty
unversioned payloads. This contradicts the intended property that accepted data
with a requested version contains that version as its first payload byte. It is
a validation issue; the reproducer does not establish an application exploit.

**F2 — checked decoding overwrites bytes after its reported output.** The `onto`
documentation says a fixed output's bytes after the final decoded byte are not
touched. Checked decoding writes payload **and four checksum bytes**, then
returns only payload length. Encoding `[42]` and decoding into a 16-byte buffer
initially filled with `0xa5` returns 1 but produces these first five bytes:

| Mode | Prefix after success |
| --- | --- |
| Base58Check | `[42,255,18,44,14]` |
| CB58 | `[42,95,73,79,193]` |

The 11 bytes after those remain `0xa5`. A one-byte buffer sufficient for the
returned payload fails with `BufferTooSmall`. Actual capacity requirement is
space for the full decoded payload plus checksum; actual unchanged suffix begins
after that full length. Keep this exception explicit in any verified contract.

**F3 — checksum error fields disagree with their public field documentation.**
`InvalidChecksum.checksum` is documented as the given checksum and
`expected_checksum` as the calculated checksum. Both mode implementations return
the calculated checksum in `checksum` and the given bytes in `expected_checksum`.
For decoded bytes `[42,0,0,0,0]`, the two errors put the corresponding computed
four-byte sequence from F2 in `checksum`, and `[0,0,0,0]` in `expected_checksum`.
The `Display` implementation follows the implementation's ordering, so this is
specifically a mismatch between the structured error fields and their docs.

Reproducer: `../../../evidence/reproduce-findings/` is an isolated Cargo package depending
on the unchanged parent crate with `check` and `cb58`, and SHA-256 0.10.9 via its
lockfile. Run from the crate root:

```sh
cargo run --locked --manifest-path ../../../evidence/reproduce-findings/Cargo.toml
```

All three behaviors are asserted, not just printed. The accompanying output log
records the run. These are executable counterexamples to desired/documented
properties, not Lean proofs or evidence that the optional checksum code was
translated by Aeneas.

## 6. Practical proof order and reporting boundaries

1. A1/A2/A3 are compact, useful targets with unrestricted 58-byte alphabet inputs.
2. Prove exact wrapper properties W1 over arbitrary inputs.
3. Prove D3's empty case for arbitrary `N`, leading-zero family for arbitrary
   input length and `N`, one-digit case for arbitrary digit and capacity, and
   arbitrary-first-invalid-byte cases. Label them restricted families, not the
   general decoder contract. For a valid alphabet and `d<58`, one symbol `a[d]`
   decodes to `[d]`, including `d=0`; thus success needs `N≥1` and pads on the right.
4. Establish the core loop invariants, B1, E1, D1, D2, and general D3; then compose R1.
5. Verify allocation/target wrappers and checksum paths separately if translation
   and dependencies are covered. Record F1–F3 instead of claiming their desired
   contracts hold.

If extraction covers only `--no-default-features`, the proof excludes `std`,
`alloc`, SHA-256/checksum modes, and optional collection targets. Opaque/missing
translated functions are exclusions or explicit trusted assumptions, not proved
code. A theorem conditional on `extracted_function(input) = expected_output` is
not a correctness proof of that function. A theorem must connect an independently
stated input condition to the actual generated computation and its observable
result, including failure/panic behavior where claimed. Closed examples are
regression evidence; universally quantified restricted families are stronger but
still do not justify calling the entire crate verified.
