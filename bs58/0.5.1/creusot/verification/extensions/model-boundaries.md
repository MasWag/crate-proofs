# Stock-model boundary probes

These diagnostic probes concern the installed, unmodified Creusot 0.13 source
revision `318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`. They are not bs58 public-API
coverage. Sources live in `extensions/probes`; raw translation, Coma, proof logs,
and input hashes live in `.work/extensions/probes`. No external specifications,
application assumptions, tool patches, or model patches were added.

## Vec adapters

Direct `Vec<u8>::resize`, `truncate`, and `as_mut_slice` compile but emit
`contractless_external_function` warnings and Coma assertions of `false` at their
calls. Their bodies therefore remain open with the installed models. See
`compile.log`, `blocked-prove.log`, and the corresponding generated Coma files.

The stock `std/vec.rs` model instead specifies `push` as exact sequence
`push_back`, `pop` as exact prefix removal, and both Vec range `IndexMut` and
`DerefMut` with initial/final sequence correspondence. This admits faithful
runtime adaptations using push-zero/pop loops and `&mut v[..]`.

`extensions/crate/src/vec_utils.rs` implements these reusable application helpers:

- `grow_zero(v,n)` requires `old_len <= n`; it ensures length `n`, preservation
  of every old byte, and zero in every appended position.
- `truncate(v,n)` requires `n <= old_len`; it ensures the exact initial
  subsequence `[0,n)`.

The exact helper bodies copied into the probe close all their generated proof
obligations (`vec-utils-prove.log`). The separate `adapted_slice` probe proves
both initial and final slice/Vec sequence correspondence. Integrating the helpers
into public wrappers requires a fresh complete extension proof; a probe itself
is not wrapper coverage. Replacing one resize/truncate call by push/pop loops
changes allocation strategy and execution cost, while preserving the specified
u8 contents and length. Allocation failure/capacity limits and termination of
allocation are outside stock `push` guarantees.

## Strings and UTF-8 repair

The following concrete callees have no installed contract, as demonstrated by
translation diagnostics and emitted `false` preconditions:
`String::into_bytes`, `String::from_utf8`, `str::as_bytes_mut`,
`core::str::from_utf8`, `Utf8Error::valid_up_to`, and `Utf8Error::error_len`.

The upstream `EncodeTarget for str` calls `as_bytes_mut`, invokes the encoder,
and relies on a Drop guard which repeatedly calls the latter UTF-8 validation
and error observers to replace invalid byte spans with NUL. Proving this exact
implementation needs models for mutable byte/string validity and UTF-8 error
positions, and a checked repair/drop argument. The current diagnostics identify
those calls; they do not establish that all alternative implementations are
impossible to verify.

The installed `std/string.rs` has a reconstruction model for unsafe
`String::from_utf8_unchecked(bytes)`: its precondition is
`exists<s: Seq<char>> s.to_bytes() == bytes@`, and its postcondition is exact
result bytes. A checked ASCII/UTF-8 witness could enable a faithful owned-string
construction adaptation. This does not model `into_bytes`, mutable `str`, error
objects, or the Drop repair algorithm. The String/str view is `Seq<char>`, with
`Seq<char>::to_bytes`; treating it as a byte sequence without that bridge is
incorrect.

## SHA-256 dependency

Probe dependencies are sha2 0.10.9 and digest 0.10.7. Compiling a dependency is
not checking its implementation. `Sha256::digest`, `Sha256::new`,
`Digest::update`, and `Digest::finalize` each emit no-contract diagnostics and
impossible call preconditions in `sha_digest.coma` / `sha_update.coma`.
No SHA model is present under the installed creusot-std source. The checksum
wrappers consequently need checked dependency contracts and implementations
(or an independently checked faithful SHA implementation), plus buffer and
error contracts. No hash oracle or assumed checksum theorem was introduced.
This is a concrete present dependency boundary, not an impossibility claim.

## Derived traits and formatting

In the application error-enum probe, the derive's call to `char::clone` yields an
arbitrary character under the installed field-call contract, so it cannot
establish exact field copying. The retained generated Clone VC in
`.work/extensions/probe27` demonstrates this precise missing postcondition.
The product extension uses a checked manual copy (`*self`) under `cfg(creusot)`
for its Copy error enums, preserving native derives and adding no external model.
All three exact-copy bodies and the six PartialEq body/refinement targets passed
the diagnostic run retained in `.work/extensions/probe28-prove.log`; integrated
product acceptance remains a separate gate.

A small u8-field type deriving Creusot `Clone`, `PartialEq`, `DeepModel` and
Rust `Copy`, `Eq`, `Debug` translates. Explicit
`use creusot_std::prelude::{Clone, PartialEq};` disambiguates their derive
macros from the Rust prelude. `Clone` and equality body/refinement targets close
in the positive probe run; no blanket claim for the different bs58 types follows.

The derived Debug body calls `Formatter::debug_struct_field1_finish`; a manual
constant-message body calls `Formatter::write_str`. Both body proofs close
under the installed `std/fmt.rs` models. Those callees have no output or result
postcondition: Coma returns an arbitrary `fmt::Result`, with only formatter
invariant requirements. Thus these proofs establish the selected body checks,
not exact Debug/Display text, formatting flags, sink call order, or propagation
semantics for a failing writer. Exact error-message verification requires an
observable formatting model and appropriate contracts; body success alone does
not establish it.

## Replay execution note

The initial positive probe run (`.work/extensions/probes/positive-prove.log`)
closed eight selected files. After adding native `cfg(creusot)` gating and
`alloc::vec::Vec` imports to the helper, the fresh diagnostic runner
`.work/extensions/probes/run-geYiX9St` translated successfully but could not
start prover processes: Why3's server-socket connect returned `Operation not
permitted`, followed by timer assertions. That replay is an environment-blocked
attempt, not a successful proof of the final fingerprint. Its logs are retained.
The integrated extension runner must establish the final helper and wrapper
proofs. The original body proof and concrete contractless-call diagnostics
remain feasibility evidence with their stated source identities.

## ASCII construction alternative

A subsequent minimal `string_push_ascii` probe builds with `String::new()` and
`String::push(*byte as char)` instead of converting/mutating byte buffers. Both
concrete calls emit impossible-precondition diagnostics in
`.work/extensions/probes/ascii-compile.log`; the generated body in
`ascii-coma/.../string_push_ascii.coma` asserts `false` at the constructor.

There is a separate byte-level gap even if character construction were adapted
through the modeled `String::from_iter<char>`: `CharExt::to_utf8` in stock
`std/char.rs` is opaque, constrained only by length between one and four and
injectivity. It supplies no theorem that a character with scalar value below
128 encodes to the singleton containing that byte. Consequently the current
models do not establish the desired exact output bytes for this alternative.
A character-sequence output contract would be a different, weaker claim. No
`string_utils.rs` product helper was added to imply byte guarantees unsupported
by the stock model. This is the specific missing bridge for the proposed ASCII
construction, in addition to the unavailable constructor/push contracts.
