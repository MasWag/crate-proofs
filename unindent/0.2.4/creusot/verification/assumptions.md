# Standard-library boundary ledger

This ledger distinguishes std models from checked application computations. No
unindent algorithm, margin calculation, byte selection or UTF-8 preservation
property may be marked trusted. All listed model sources and actual tool/dependency
binaries must be identified in the integrated evidence fingerprint.

## Frozen standard models

Creusot/creusot-std 0.13 models the selected Rust integer operations, `u8`, slice
contents/indexing, vector contents/updates, options/results and character/string
views. Vector construction starts with an empty sequence and `push` appends the
given value. These models do not verify the internals of Rust's standard library,
allocator availability, capacity/pointer identity or operating-system resources.
Actual resolved dependency sources must be captured from Cargo metadata.

The logical string view is a sequence of Unicode scalar values; byte contents
are related through the frozen character encoding operation. Scalar/byte equality
must not be assumed merely because two unrelated views have matching lengths.

## Additional explicit UTF-8 models

The frozen character encoding abstraction exposes insufficient byte facts for
ASCII deletion. The following narrow std encoding facts were independently
reviewed by the Astra specification agent as true for Rust UTF-8 encoding:

1. Each ASCII scalar (`c < 128`) encodes as exactly its one corresponding byte.
2. Every byte of a non-ASCII scalar's UTF-8 encoding is at least 128.

They apply to standard character encoding, including NUL, CR, LF, SPACE and TAB;
they state no fact about this application's output. Existing encoding-length and
sequence definitions remain part of the frozen std model. Checked lemmas must
derive preservation of valid encoding when complete ASCII bytes are erased,
using these laws and the actual application's proven erasure relation.

The additional `str::as_bytes` boundary exposes exactly the standard UTF-8 byte
encoding of the string view. The `String::from_utf8` model returns `Ok` exactly
for a byte sequence with a valid encoding witness, preserving those bytes in the
result; the invalid case returns `Err`. Error internals are not observed by this
application and are not covered. The caller must prove validity before relying
on successful conversion and `unwrap`.

The character encoding facts and external std specifications are trusted
boundaries, not successful application proof targets. Application erasure,
encoding-concatenation/preservation lemmas and all caller obligations must be
checked with positive proof goals. Any further model extension needs a separate
scope review and ledger update.

## Source and allocation limits

The mathematical byte contract covers all representable input contents; byte
inputs are not restricted to valid UTF-8. The string contract relies on the Rust
`str` type's validity and must establish output validity. Allocation failures and
external resource exhaustion remain outside the std model. An adapted source's
proof plus finite native agreement does not establish a formal correspondence
theorem for the released iterator implementation.
