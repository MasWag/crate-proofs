# Independent specification for further bs58 0.5.1 coverage

This extension preserves the accepted four-core proof inputs. Astra owns this
contract design; Sol owns implementation. This file specifies obligations, not
completed proofs. [Coverage inventory](coverage.md) separates candidates and
semantic limitations; the extension run report must supply actual statuses.
The reference is the unchanged release source described in the parent source
lock. `E_A`, `D_A`, `encoded`, `decoded`, `encode_fits`, `decode_fits`, and exact
error relations have the meanings fixed in [the core specification](../specification.md).
Alphabet validity includes distinct ASCII control bytes and NUL.

## Builder state and public calls

For both builders, `new(input, alpha)` retains the input and alphabet and sets
`Check::Disabled`; the crate-private `from_input` uses `Alphabet::DEFAULT` with
disabled checking.
`with_alphabet` replaces only the alphabet, preserving input and check mode.
`with_check`, `with_check_version`, and `as_cb58` change only the corresponding
mode/version field. Top-level `encode` and `decode` return the appropriate
`from_input` result. An adaptation calling `new(input, Alphabet::DEFAULT)` must
establish the same fields and record that construction-path change. These state
contracts do not assume input validity.
Proving constructors alone is not a codec proof or cross-tool composition.
Default construction must connect the actual default constant to the valid
Bitcoin table; it cannot assume an arbitrary unverified constant is valid.

For disabled checking and concrete slice input/target, `EncodeBuilder::onto`
inherits the complete `encode_result`, including capacity failures and unchanged
successful suffix, after evaluating the original maximum-length arithmetic.
`DecodeBuilder::onto` similarly inherits `decode_result`, including its
capacity-dependent error ordering. Decoding into `[u8; N]` is the same operation
on all N bytes, not the zero-initialized/padded const-array operation.

The proof must preserve actual trait dispatch: `onto` invokes `encode_with` or
`decode_with`; `[u8]` invokes the callback once with the same full mutable slice
and returns its result; decode `[u8; N]` invokes it on the whole array coerced to
a slice; `&mut T` delegates to `T` with the same maximum length and callback.
Replacing these paths by a direct core call only proves a specialized adapter,
unless the bypassed dispatch and callback relation are also checked.

Arbitrary legal targets need not invoke the callback at all. Therefore the
generic `onto` theorem is an operational composition with the target's checked
contract, not an unconditional claim that every `EncodeTarget` or `DecodeTarget`
contains Base58 output. Callback pre/postconditions, termination assumptions,
and generated trait refinements belong in the evidence inventory.

Arbitrary `AsRef<[u8]>` implementations need not be stable. Unchecked encode
captures one slice and passes that slice to its callback. Decode calls `as_ref`
once for the advertised maximum length and again inside the callback; checked
encode also repeats it. A generic input contract must distinguish those
observations or require and establish stability for a concrete implementation.
Slice specialization is legitimate, but does not prove all `AsRef` inputs.

## Length arithmetic and allocation

Let `M=usize::MAX` and `h(n)=n+floor((n+1)/2)`. `max_encoded_len` returns exactly
`h(n)` without overflow when `n<M` and `h(n)<=M`. Its intended capacity theorem
is `len(E_A(x))<=h(len(x))`, including empty and all-zero inputs. The inequality
needs a checked radix/width proof; proving the machine arithmetic is separate.
The original public encoder evaluates this expression even for fixed targets.
Real Rust byte slices are bounded by the addressable allocation domain, which
can make this bound automatic on the selected platform; any such use must come
from the actual shipped model rather than an unrecorded assumption.
The decode bound is `len(D_A(s))<=len(s)` for valid-symbol sequences.

For a growable byte target with old contents `p`, requested size `q`, and callback
`f`, preserve this order:

1. Compute `original+q` and resize to `p ++ zeros(q)`.
2. Invoke `f` on exactly the appended q bytes.
3. On `Ok(k)`, truncate to `original+k` and return `Ok(k)`.
4. On `Err(e)`, return `Err(e)` before truncation: the buffer retains length
   `original+q`, preserves p, and contains the callback's modified tail.

For codec callbacks `0<=k<=q`; a standalone arbitrary-callback adapter cannot
silently assume that law. Upstream `truncate` does not grow the vector when k
exceeds q, and `original+k` itself can overflow for a hostile callback result.
For safe codec composition, require machine addition bounds and the allocation
domain, establish the callback range from its checked contract, and distinguish
resource exhaustion from modeled correctness. The unchecked encoder appends
exactly `E_A(x)` and returns its length. The unchecked decoder appends `D_A(s)`
on success; with q equal to the stable input length, character errors remain
possible but numeric capacity failure does not. Its failure retains the enlarged
buffer, not p alone. `into_vec` starts with an empty vector, returning exactly
the output on success; decode propagates errors and discards its local buffer.

SmallVec and growable TinyVec have the same resize/callback/truncate behavior
but require their own dependency contracts. Fixed-capacity tinyvec ArrayVec and
SliceVec invoke the callback on spare capacity, update logical length only on
success, and preserve their old logical length on failure; spare memory may
change on failure. They do not implement resize semantics.

## Strings and unsafe string targets

`String::encode_with` first takes the old string, leaving the target empty,
encodes via the vector adapter, and restores the String only after successful
UTF-8 conversion. A codec success appends ASCII output to the original UTF-8
bytes. Callback error leaves the target empty. An arbitrary callback can produce
invalid UTF-8, making the final unwrap panic; the trait signature alone does not
exclude this. `EncodeBuilder::into_string` has bytes exactly `E_A(x)` when the
length/allocation obligations hold. ASCII membership must be derived from valid
alphabet/core output, not imposed as a new alphabet restriction.

The mutable `str` adapter is different: it calls the callback on the original
bytes using unsafe `as_bytes_mut`, then runs its drop guard's UTF-8 repair even
on an error or unwind. The repair repeatedly preserves valid spans and replaces
invalid UTF-8 spans or an incomplete trailing sequence with NUL bytes. Successful
codec output remains intact; immediately after its prefix, up to three bytes of
a partially overwritten original scalar can become NUL; the later suffix stays
unchanged. On codec failure the scratch output may be arbitrary bytes and repair
may affect more than three bytes. No raw-byte suffix theorem on failure or generic
callback success is implied. Verification needs actual UTF-8 validation,
byte-view/mutable-view, and drop/unwind relations supported by the unchanged
toolchain; missing relations must be logged individually, not axiomatized.

## Const wrappers and alphabet conveniences

`into_array_const::<N>` requires disabled checking to avoid its explicit assertion
and returns the existing exact padded `decode_const_result`. Enabled checking
panics even for otherwise valid inputs. `into_array_const_unwrap::<N>` additionally
requires `decode_fits(input,A,N)` for a no-panic proof and returns `D_A(input)`
followed by zeros. It does not require decoded length N. Errors deliberately
panic through `Error::unwrap_const`; that diverging API cannot be honestly given
an unconditional no-panic theorem.

`Alphabet::new_unwrap` returns exactly the successful constructor's tables for
distinct ASCII input and deliberately panics on invalid bases. Preserve its
original out-of-bounds-array panic path or document any changed runtime behavior.
The built-in alphabet constants require evidence for their particular byte arrays;
MONERO is independently constructed from the same 58 alphabet bytes as BITCOIN,
so its tables must be equal; no pointer-identity claim follows. DEFAULT is
defined as `Self::BITCOIN`. Native const evaluation and
formal verification of a runtime-adapted body are distinct claims.

## Iterators, round trips, and checked modes

The generic encoder consumes `input.clone()` for numeric value and the original
iterator's initial zero run for padding. Bare `Clone + IntoIterator` does not
guarantee equal finite sequences, termination, or side-effect freedom. Its general
operational output has numeric digits from the clone's sequence and leading-zero
count from the original sequence. A conventional Base58 theorem requires a
checked equality/finiteness bridge for the concrete iterator, including checksum
chains. Neither an unchecked clone law nor silent materialization of a hostile
iterator is a faithful proof of the generic implementation.

Round-trip obligations are `D_A(E_A(x))=x` and, for alphabet-only s,
`E_A(D_A(s))=s`. Prove uniqueness of byte/base58 representations including exact
leading counts. Numeric equality alone is insufficient. Implementation composition
additionally proves both calls succeed with chosen capacities and relates the
actual returned prefixes; fixed-array padding is not part of the decoded payload.

Checksum setters are state updates and do not establish SHA correctness. Full
checked encoding prepends the optional version and appends the appropriate four
digest bytes before Base58 conversion. Checked decode first performs the entire
core decode; then tests length>=4, checksum equality, and requested version in
that order. It returns payload length including any version, without stripping
the first byte. Preserve the recorded findings: checksum-only data can satisfy
the version comparison using the first checksum byte; checksum bytes were written
beyond returned length; `InvalidChecksum` fields contain computed and encountered
values in the order opposite to their documentation. Existing findings refute
stronger desired properties, not verification of the actual branches. Full digest
claims require checked dependency behavior under unchanged infrastructure.

## Acceptance boundary

No trusted application routine, unchecked iterator/target law, weaker error
contract, or modified standard-library model is permitted. Each model limitation
must identify the actual missing method/relation and a retained diagnostic or
source inspection, with untested boundaries labeled untested. Exclusion from the
old core scope alone is never a blocker. Freeze specification, coverage, source,
and dependency pins before a fresh run; enumerate positive body obligations,
helper obligations, and trait refinements separately. Finite release comparisons
are correspondence evidence, not formal all-input equivalence.
