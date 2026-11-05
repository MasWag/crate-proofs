# Independent contract and model review

Reviewer role: specification/correctness agent, separate from the Sol agents
implementing the runtime adaptation and proof bodies. Review date: 2026-11-05.
This review applies the Creusot verification, proof-composition and proof-report
skills. It reviews the contracts and their mathematical meaning; final run
acceptance and evidence freshness remain the primary's responsibility.

## Verdict

The selected byte core and concrete string/byte extension contracts express
substantive exact functional correctness for the adapted implementation. They
do not restrict byte contents, require positive indentation or assume UTF-8 for
the byte API. String conversion success follows from an application preservation
proof built on narrow standard encoding assumptions, not from a trusted
application theorem. Termination is selected explicitly for runtime targets;
recursive ghost proofs and runtime loops have decreasing variants.

The checked contents relation is `spec::source_unindented`, a complete ordered
source-position characterization. It is not merely an output-length bound, a
partial subsequence relation or an operational recurrence copied from the loop.
The independent decomposition/minimum relation `spec::unindented` remains a
separate specification. The mathematical equivalence argument in
`specification.md` was reviewed, but there is no machine-checked equivalence
theorem between these two relations. A claim about the raw checked theorem must
name the source-position relation and keep this formal bridge visibly open.

## Scope and successful-return meaning

- `unindent_bytes` and its flagged private core guarantee exact retained bytes,
  input-relative non-growth and termination, for every representable input slice.
- `unindent` and its flagged private wrapper guarantee the corresponding exact
  output bytes and non-growth. The `String::from_utf8(...).unwrap()` path is
  selected; its successful return depends on checked UTF-8-preservation helpers.
- The concrete `[u8]`, `str` and `String` extension implementations carry the
  corresponding contents/length/termination contracts. Their generated
  refinement goals must be included in the final generated inventory.
- The generic reference implementation remains available natively but is
  excluded from Creusot selection. No arbitrary downstream implementation is
  assumed total or required to satisfy this crate's byte transformation.

The subject is a verification adaptation: indexed margin discovery followed by
a bytewise retention scan. Neither these contracts nor finite native comparisons
prove all-input equivalence to the original release's iterator implementation.
The unchanged release, adapted implementation, original Aeneas results, native
tests and Creusot proof are distinct evidence subjects.

## Important contract checks

The margin is an attained minimum over exactly the later nonblank fields, with
zero when none exists. This excludes an incorrect always-zero margin while
preserving the first-line exception. SPACE and TAB are the only indentation
bytes, each contributing one byte. The initial CR of CRLF is removed, and an
interior CR-only field remains nonblank and forces margin zero as in the release.

The trace requires strictly increasing source indices, exact byte equality and
completeness for every retained position. It therefore excludes extra, omitted,
duplicated or reordered bytes. The accumulated vector length is bounded by the
processed source prefix, supporting the final non-growth contract and bounded
intermediate output size. Scan bounds and loop variants address arithmetic,
indexing and termination separately from contents.

The UTF-8 bridge proves every byte at least 128 is retained, derives ordered
ASCII-only erasure from the complete trace, and proves that such erasure preserves
the character-encoding witness. This suffices because deleting ASCII cannot
split a multibyte UTF-8 encoding. Sequence extensionality, head/tail
reconstruction, slice/concatenation laws and witness shifts are checked helper
contracts. Their empty bodies, where present, generate proof obligations; they
are not marked trusted.

## Reviewed trust boundary

The only application-local `trusted` declaration reviewed is
`utf8::encoding_laws`, explicitly a standard-library model extension:

1. An ASCII scalar's encoding is the singleton byte with that scalar value.
2. Every encoded byte of a non-ASCII scalar is at least 128.

These are sound facts about standard UTF-8. They supplement the frozen
`char::to_utf8` abstraction, which by itself does not export those byte facts.
They do not assume that unindent preserves UTF-8. The frozen character/scalar
model and its valid-char invariant remain part of the standard-library model.

The external `str::as_bytes` contract relates bytes to the string's character
encoding. The external `String::from_utf8` contract gives exact bytes on success
and invalidity on failure; together these branches imply successful conversion
for a valid encoding witness. Both have modeled termination. Their declaration
is not verification of the standard library implementation.

Standard sequence, vector, slice, integer, String and allocation models remain
ambient trust. In particular, this proof is not evidence of memory availability,
allocator success on the host, physical capacity behavior or pointer identity.
No application algorithm, U-preservation claim, margin computation or output
trace is trusted or supplied through an unchecked application extern contract.

## Source identities reviewed

SHA-256 hashes relative to the Creusot workspace:

| File | SHA-256 |
|---|---|
| `src/lib.rs` | `5c2ef34ec14de773aeed1affbc8a256b96429793c7daa240fa1cdd9611baa8e9` |
| `src/spec.rs` | `59245b4728a499e15bb957597aa126cb79d4555a7e7724312d5216f0337ff7ef` |
| `src/lemmas.rs` | `12be72329bde281f7700f04f7c39c14de9cb90046e0a7bf5efb5b425636dc1d2` |
| `src/utf8.rs` | `76b96d398b0bae2293ef98bbf956f071930364b006f3e6ff750dc31a16473cf8` |
| `src/utf8_trace.rs` | `7d54d639cb2e1768b46f5aceea7b8bdb71b0a4b56ce75e7d1a1d619fb40ab39c` |

Final acceptance requires the integrated fresh-run manifest to match these
sources, include all selected positive roots and helper/refinement goals, close
every leaf, record successful process status, and preserve input/tool hashes.
Isolated diagnostic closure does not replace that integrated run. Current run
counts and outcomes belong to the results record, not this input review.
