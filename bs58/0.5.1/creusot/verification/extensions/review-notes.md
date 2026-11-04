# Independent extension review

This is a source/specification review of the evolving extension, not acceptance
of a fresh verification run. Integrated proof/native evidence and fingerprints
have not yet been supplied for final review. The accepted four-core evidence
remains separate. Astra reviews specifications; Sol owns proof implementation.

The review read the original and extension specifications and coverage, original
results, extension model-boundary ledger, wrappers, vector helpers, and initial
round-trip relations. Applicable guidance was read from `publication/AGENTS.md`,
the version and Creusot AGENTS files, and
`publication/.agents/skills/{creusot-verification,creusot-proof-composition}/SKILL.md`.

## Current semantic assessment

- Slice encoder/decoder wrappers retain the existing complete result predicates,
  including errors and unchanged successful suffix. Decode array dispatch uses
  the whole existing array, unlike the padded const result.
- Slice and array target bodies invoke the actual callback; `&mut T` bodies
  forward the same callback and length to T. The added trait contract describes
  a restricted whole-buffer callback relation. It is not a law satisfied by
  every legal upstream target. The concrete implementations and all generated
  refinements must close before accepting their use in callers. The logical
  contract records the callback relation; invocation count also relies on the
  reviewed concrete single-call bodies, not an independent observable trace.
- Slice input specialization makes repeated `AsRef` observations stable. It
  does not establish stability for arbitrary user-defined `AsRef` implementations
  or equal clone/original iteration for arbitrary iterators.
- `Check` has only `Disabled`. This is a default-feature specialization, not
  coverage of checksum setters or enabled-mode behavior. Constructor field
  contracts retain input/alphabet; disabled state follows from the sole variant.
- `max_encoded_len` has its exact arithmetic contract with explicit overflow
  domain. The condition `n + (n+1)/2 <= usize::MAX` also excludes `n=usize::MAX`;
  there is no missing inner-addition domain in that formula. This arithmetic
  theorem alone does not prove that the result accommodates encoding.
- Vector methods are specialized direct-core adapters, not proofs of the
  upstream vector target's generic callback/trait dispatch. Their ordered
  growth, core call, error return, and successful truncation match the intended
  u8 contents/length behavior. Growth and truncation helpers preserve exact
  sequences in their restricted upward/downward domains. Their allocation
  strategy differs from upstream resize/truncate and is documented separately.
- Vector result contracts preserve the old prefix, give exact successful
  appended payload/length, and retain enlarged length on error. Error-tail
  bytes are unconstrained, matching the original core failure relation; do not
  describe this as an exact all-byte error-state theorem. The encoder contract
  still permits `BufferTooSmall` at the advertised bound. Unconditional encoding
  success and exclusion of numeric decode capacity errors need separate checked
  width bounds; these intended obligations must remain visible if unfinished.
- Const unwrap has the appropriate explicit fit precondition and padded success
  relation. Alphabet unwrap retains the original out-of-bounds panic mechanism
  and has a valid-base success domain; no invalid-input no-panic claim follows.
- Initial round-trip lemmas include positional uniqueness and exact leading-zero
  counts. Their conclusions are conditional on both codec relations. These are
  not yet existence/capacity theorems or successful composed runtime calls.

## Subsequent pre-run inspection

The added correspondence document correctly distinguishes whole-slice trait
dispatch from the direct-core vector adaptations and records the allocation
and generic-input boundaries. New vector-returning convenience methods and
an exact-copy Alphabet Clone implementation are present. Their body and
refinement obligations remain subject to the integrated inventory.

`encode_decode_roundtrip` now composes actual encoder and decoder calls, with
checked capacity lemmas and mathematical round-trip relation invoked in the
body. This is the right shape for a runtime composition theorem. Its capacity
lemmas and all client goals still need final evidence; the earlier conditional
relation lemmas alone do not establish it. At this inspection, encoder
`into_vec` still requires `encode_fits` explicitly; the implementation owner
was asked to discharge it internally using the capacity theorem once available,
so the public contract matches the intended arithmetic-only domain.

The extension runner uses a fresh generated/target directory, proves every
generated Coma file, demands a nonempty required-target list, fingerprints the
source/specifications/coverage/scripts/tool configuration, and invokes the
original guarded root reconstruction and computational replay checker. The
required-target inventory is still pending at this inspection. Final acceptance
requires comparing it to actual body/refinement/helper roots, not merely
observing the runner's successful exit. Reported diagnostic native comparisons
are not treated here as a final fingerprint-matched native run.

## Remaining acceptance gates

Re-read the final frozen source and coverage. Check positive roots and complete
trees for every selected body, helper, generated implementation, and trait
refinement; inspect actual call targets in generated Coma. Distinguish computed
closures from solver leaves and retain independent replay evidence. Check
before/after source, specification, configuration, dependency and tool/model
fingerprints, successful exits, and absence of unchecked application assumptions.
Confirm native comparisons match the final runtime adaptation and report them
separately from formal proof. The model-boundary probes establish only their
precise diagnosed missing contracts, not impossibility of verifying entire API
families. Default tables/from-input/top-level constructors, allocating convenience
methods, checked modes, strings and other unimplemented inventory entries must
not inherit coverage from nearby proved routines.

## Final contract inspection before integrated run

The subsequent source resolves the capacity gaps noted above. `encode_capacity`
has no input-fit assumption: its proof uses positional magnitude after leading
zeros and the inequality `256^n <= 58^(n+(n+1)/2)`, reducing two source digits
against three output digits. `decode_capacity` applies to alphabet-only input.
`valid_prefix_capacity` and `decode_no_buffer_error` additionally exclude numeric
capacity errors for invalid input when capacity is the full input length; they
do not assume the entire input is valid. Both capacity results include empty
and all-zero sequences.

Encoder `onto_vec` now guarantees success under valid alphabet and machine
length-sum bounds. Encoder `into_vec` discharges capacity internally and no
longer requires `encode_fits`. Decoder vector methods guarantee success for
valid symbols and exclude `BufferTooSmall` for every input; precise character
errors still use `decode_error`. Prefix preservation and enlarged error length
remain guaranteed, with error tail bytes unconstrained. This meets the intended
functional domains without excluding malformed inputs.

The concrete runtime client composes encoding then decoding and promises exact
original bytes. The reverse direction is currently a mathematical relation
theorem, not a second runtime client. Positional uniqueness includes exact
leading-zero counts and alphabet-symbol inversion. No unchecked application
law was identified in these bodies. These conclusions concern contract shape
and source review; diagnostic successes do not replace the fresh full run.

Runtime wrappers and vector loops do not currently carry termination attributes.
Do not extend recursive mathematical variants or original core termination
claims to an unconditional termination theorem for every extension routine.
In particular, arbitrary callbacks can fail to terminate; their target relation
does not establish callback termination.

## Source identity clarification

The release does contain crate-private `from_input` constructors at
`src/encode.rs:219` and `src/decode.rs:208`; top-level functions call them at
`src/lib.rs:220` and `src/lib.rs:171`. All four inspected release source files
(those three plus `alphabet.rs`) matched the parent source-lock SHA-256 values.
The independent inventory now explicitly labels this constructor crate-private.
An adapted frontend calling `new(input, DEFAULT)` instead has the same intended
field contract but is a changed construction path. MONERO is constructed
independently from Bitcoin's same bytes; the specification requires table
equality, not pointer equality. DEFAULT is explicitly `Self::BITCOIN`.
