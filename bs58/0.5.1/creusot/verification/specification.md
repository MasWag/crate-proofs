# bs58 0.5.1: independent Creusot specification

This document fixes the intended contracts for the Creusot verification fork of
bs58 0.5.1. Astra owns these specifications; Sol owns the runtime adaptation and
proof implementation. It is an obligation inventory, not a claim that the
obligations have been proved. The run manifest and coverage record must identify
which function bodies, mathematical lemmas, and correspondence bridges have
actually been checked by the unmodified Creusot toolchain.

The reference implementations are `bs58/src/alphabet.rs::Alphabet::new`,
`bs58/src/encode.rs::encode_into`, and
`bs58/src/decode.rs::{decode_into,decode_into_const}` in the shared workspace.
The historical Aeneas profile and its evidence remain separate and unchanged.
Release provenance comes from the parent version's `source.lock.json`; a matching
version string alone does not establish source identity.

## 1. Mathematical meaning, independent of the conversion loops

For a finite digit sequence `s`, define the big-endian value

`BE_b(s) = sum(s[i] * b^(len(s)-1-i), i=0..len(s)-1)`.

Define `LE_b(s)` with exponent `i` instead. Empty sequences have value zero.
`digits_b(v)` is the unique big-endian base-`b` representation of nonnegative
integer `v`, with no leading zero; `digits_b(0)` is empty. `leading(s,z)` is the
length of the maximal initial run of byte `z`.

A valid alphabet consists of 58 distinct ASCII bytes `a` and an inverse table
`t` of length 128. For every ASCII byte `c`, `t[c]` is its unique index in `a`
when present, and 255 otherwise. All ASCII values, including NUL and control
characters, are allowed. There is no printable-ASCII precondition.

For any byte sequence `x`:

`E_A(x) = repeat(a[0], leading(x,0)) ++ map(a, digits_58(BE_256(x)))`.

For any sequence `s` containing only alphabet symbols:

`D_A(s) = repeat(0, leading(s,a[0])) ++ digits_256(BE_58(map(t,s)))`.

These equations determine the complete output, including empty and all-zero
inputs. Their independent value-and-leading-count characterization is used in
`crate/src/spec.rs`:

* `encoded(x,y,a,t)` says every byte of `y` belongs to the alphabet,
  `BE_58(map(t,y)) = BE_256(x)`, and
  `leading(y,a[0]) = leading(x,0)`.
* `decoded(s,y,a,t)` says `s` belongs to the alphabet,
  `BE_256(y) = BE_58(map(t,s))`, and
  `leading(y,0) = leading(s,a[0])`.

With a valid alphabet these predicates uniquely determine `y`, and are
equivalent to `y=E_A(x)` and `y=D_A(s)` respectively. This follows from uniqueness
of positional representation after removing the exact initial zero run. A
numeric-value equation alone would be insufficient: arbitrary leading zeros
would satisfy it. The formal contracts retain the leading-count conjunct.

The executable ghost definitions are `pow`, `be`, `le`, `digit`, `be58`, and
`leading`. For totality outside its intended domain, `pow(b,n)` is defined as 1
when `n <= 0`; codec uses have nonnegative exponents. `digit` returns 255 for
non-ASCII inputs or an incorrectly sized inverse table. This makes the model
total; codec contracts still require a valid alphabet. `be58` may consequently
evaluate invalid bytes as sentinel digits, but success and prefix-error
conditions only use it on prefixes proven valid.

## 2. Alphabet construction: unrestricted inputs and exact errors

`Alphabet::new` has no alphabet-validity precondition. For every input array of
58 bytes it terminates without panic and satisfies `alphabet_result(base,result)`.

* `Ok(A)` occurs exactly when all bytes are ASCII and pairwise distinct.
  `A.encode` equals the input array, and every entry of `A.decode` satisfies the
  inverse-table definition, including 255 for absent characters.
* Let `j` be the first index that is non-ASCII or duplicates an earlier byte.
  If the byte is non-ASCII the result is `NonAsciiCharacter {index:j}`.
  Otherwise the result is `DuplicateCharacter {character:char(base[j]),first:i,
  second:j}`, where `i<j` is the unique earlier matching index.

The constructor tests non-ASCII before indexing the inverse table. The prefix
before the returned index must be ASCII and injective, so a later fault cannot
replace the earlier one. The invalid-input cases must not be discharged by
adding a valid-base precondition.

`alphabet_prefix(base,encode,decode,n)` states that the processed input prefix is
valid, its bytes have been copied to `encode`, and the entire inverse table is
exact for that prefix. A table entry is either the unique processed index or
255 with no processed occurrence. This supplies both forward/inverse laws at
termination and the earliest-occurrence evidence at a duplicate error.

The alphabet laws are postconditions established by construction. They are not
assumptions about arbitrary arrays. The proof fork's public table fields permit
construction of malformed values, so the codec precondition is explicit; this
is a proof interface change, not a claim that upstream exposes those fields.

## 3. Encoder: complete output, capacity, and untouched suffix

For a valid alphabet, arbitrary finite input bytes `x`, and any initial mutable
buffer `old` of length `m`, the slice adaptation of `encode_into` must satisfy:

* If `len(E_A(x)) <= m`, it returns `Ok(len(E_A(x)))`, writes exactly `E_A(x)`
  into the output prefix, and preserves `old[len(E_A(x))..m)` byte for byte.
* Otherwise it returns `BufferTooSmall` without panicking. No unchanged-buffer
  or rollback guarantee is made on failure.

`encode_result` encodes these alternatives. Its capacity predicate avoids
floating-point logarithms and recursive digit construction. Set
`z=leading(x,0)` and `V=BE_256(x)`. Then

`encode_fits(x,m) <=> z <= m && V < 58^(m-z)`.

This is exactly the sufficient-and-necessary output-capacity condition,
including `V=0`, empty input, and capacity zero. The success predicate fixes the
returned length via the complete output relation; it is not merely an upper
bound on the output length.

Upstream's private encoder is generic over `I: Clone + IntoIterator<Item=&u8>`.
Those Rust bounds alone do not imply that the clone and original enumerate the
same sequence, terminate, or have no side effects. The slice adaptation verifies
the finite sequence domain. To transfer it to a concrete upstream call site,
establish that the first and second iterations enumerate the same finite byte
sequence in the same order. The ordinary slice call site has this property.
Checksum chains need their own construction and iterator-law bridge. No theorem
for arbitrary implementations of `Clone + IntoIterator` is claimed.

## 4. Decoder: complete output and capacity-dependent error order

For a valid alphabet, an alphabet-only input `s`, and an initial output buffer
`old` of length `m`:

* Success occurs exactly when `len(D_A(s)) <= m`, returns that exact length,
  writes `D_A(s)` into the prefix, and leaves the suffix of `old` unchanged.
* Otherwise the result is `BufferTooSmall`; the buffer may have been modified.

Writing `z=leading(s,a[0])` and `V=BE_58(map(t,s))`,

`decode_fits(s,A,m) <=> s contains only alphabet symbols && z <= m && V < 256^(m-z)`.

For invalid input, let `j` be the first byte outside the alphabet, and let
`p=s[0..j)`. The result is precisely:

* If `BE_58(map(t,p)) >= 256^m`, return `BufferTooSmall` before reaching `j`.
* Otherwise, return `NonAsciiCharacter {index:j}` if `s[j]>=128`, or
  `InvalidCharacter {character:char(s[j]),index:j}` if `s[j]<128`.

Only the numeric width of `p` matters here. Leading zero symbols are appended
after the complete validation/numeric-conversion pass. For Bitcoin alphabet
and output capacity zero, input `"10"` reports invalid `'0'` at index 1, while
`"20"` reports `BufferTooSmall`. A contract that validates the entire input
before checking capacity, or charges leading zeros before validation, would
change observable behavior.

`decode_error` expresses the same precedence without a partial first-error
function. For `BufferTooSmall`, it requires either a valid prefix with numeric
value at least `256^m`, or an entirely valid input failing `decode_fits`.
For a character error it requires a valid prefix before the reported byte,
the exact offending byte/class, and numeric-prefix value less than `256^m`.
Nonnegative radix digits make prefix values monotone, so the latter condition
also excludes an earlier numeric capacity failure. These alternatives exhaust
all inputs and do not overlap under the valid-alphabet precondition.

## 5. Const decoder: right padding, not an exact-size assertion

`decode_into_const::<N>` has the same capacity and error selection as the
ordinary decoder with capacity `N`. On successful valid input its entire result
is

`D_A(s) ++ repeat(0, N-len(D_A(s)))`.

It permits decoded length less than `N`; it neither requires equality nor adds
padding on the left. `decode_const_result` requires the complete decoded prefix
and every remaining array element to be zero. The prefix length is determined
by `decoded`, even though the public result does not return that length. Empty
input succeeds for every `N`, producing an all-zero array; an input consisting
of `k` zero symbols succeeds exactly when `k<=N`, also producing all zeros.

This contract concerns the unchecked private core. The public const builder
rejects enabled checksum mode through an assertion. No checksum support is
inferred from the unchecked-core result.

## 6. Proof decomposition and arithmetic invariants

For encoding use target radix `R=58` and source multiplier `S=256`; for decoding
use `R=256`, `S=58`, and alphabet-decoded source digits. At the outer loop head,
the active output prefix is a little-endian representation of the consumed
input value. Its digits lie in `0..R`; it is empty for value zero and otherwise
has a nonzero final digit. The inactive output suffix equals the initial buffer.

For an old active prefix `old_digits` of length `k`, source digit `d`, and
processed inner-loop length `j`, a convenient snapshot invariant is

`LE_R(new_digits[0..j)) + R^j*carry = S*LE_R(old_digits[0..j)) + d`.

An equivalent invariant avoiding a snapshot is

`LE_R(output[0..j)) + R^j*carry + S*R^j*LE_R(output[j..k)) = next_input_value`.

Once all old digits are processed, the extension loop invariant is

`LE_R(output[0..index)) + R^index*carry = next_input_value`.

Together with digit bounds, nonnegativity, and normalization, this explains both
successful conversion and the capacity error: positive remaining carry at
`index=m` implies the new value is at least `R^m`.

Encoding carry is at most 255 at iteration boundaries; decoding carry is at
most 57. Their intermediate arithmetic is bounded by
`255 + 57*256 = 57 + 255*58 = 14847`, so these steps fit every supported Rust
`usize`. Bounds must also justify indexing, casts, division, bitwise masking,
shifts, and loop-counter increments. A no-panic proof for an adequately sized
buffer alone is not the total error-inclusive contract.

After numeric conversion, append exactly the leading-zero count, map encoding
digits through the alphabet where appropriate, and reverse the active prefix.
Preserve the unmodified suffix through every phase. The const decoder starts
from a zero-filled array, which turns this same suffix preservation into its
right-padding postcondition.

The model file includes checked candidate lemmas `be_step`, `be58_step`,
`le_split`, and `pow_positive`; they are ordinary proof obligations, not trusted
facts. Further useful checked lemmas include radix-value nonnegativity,
digit-value upper bounds, powers/addition, reversal, leading-count bounds,
normalization/width equivalence, and the capacity monotonicity relation. A
complete run must include all used helper lemmas and their dependencies.

## 7. Scope, correspondence, and reporting boundaries

The required core scope is all finite byte inputs and all output capacities for
the four stated functions, subject only to valid alphabets for codecs. There is
no bounded test-size restriction. No trusted application function, assumed
algorithm contract, or unchecked arithmetic lemma may establish these claims.
Unproved intended postconditions remain open obligations; removing them from
the source does not turn a weaker result into complete correctness.

Rust adaptations must record a function map, source hashes, changed executable
lines, and reasons. Index-based loops may replace slice iterators and explicit
capacity checks may replace `get_mut(...).ok_or(...)`, provided iteration order,
error selection, writes, and arithmetic are preserved. Native differential
tests are useful evidence for these changes but are not a formal proof of
equivalence to the release for all inputs.

Optional checksum paths, SHA-256, allocation targets, formatting, unsafe mutable
string adapters, and whole-crate API coverage are outside this core contract.
The previously recorded checksum findings remain relevant but are not new
Creusot theorems: checksum-only data can be accepted with an expected version;
checked decoding writes checksum bytes beyond its reported payload length;
and the two `InvalidChecksum` fields are populated opposite to their field
documentation. No desired property contradicted by those findings should be
silently assumed in a future checksum extension.

Possible later mathematical results are `D_A(E_A(x))=x` and `E_A(D_A(s))=s`.
Calling the implementations mutual inverses additionally requires composing
their proved contracts and discharging the chosen output-capacity conditions.
The `max_encoded_len` implementation and allocation-size arithmetic require
separate machine-overflow contracts; they are not established merely by the
core radix arithmetic bounds.
