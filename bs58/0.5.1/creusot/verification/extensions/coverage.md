# Extension API obligation inventory

This is the independent selection/feasibility inventory, not a proof-results
page. All entries require fresh extension evidence before being called verified.
The unchanged four-core result remains in [the accepted results](../results.md).
Intended contracts are in [the extension specification](specification.md).

| Release API / family | Priority and required obligation | Limitation classification |
| --- | --- | --- |
| EncodeBuilder/DecodeBuilder `new`, crate-private `from_input`, `with_alphabet`; top-level `encode`, `decode` | First: exact fields, default table bridge | Release frontends call `from_input`; an adapted `new(input, DEFAULT)` path needs corresponding field contracts; previous Aeneas result is separate |
| Builder `with_check`, `with_check_version`, `as_cb58` | First: exact mode/version update | Does not verify subsequent checksum computation |
| `EncodeTarget for [u8]`, `DecodeTarget for [u8]` and `[u8;N]` | First: same slice, callback exactly once, result and mutation propagation | Actual higher-ranked closure and dispatch models must be probed |
| Both target traits' `&mut T` implementations | First: exact delegation preserving concrete dispatch | Must check generated trait refinements, not just forwarding body |
| Disabled `EncodeBuilder::onto` and `DecodeBuilder::onto` | First: complete existing codec relations through concrete targets | Generic target correctness is false without a target law; generic AsRef stability not guaranteed |
| `max_encoded_len` | First: exact overflow-bounded arithmetic; then sufficient bound | Capacity theorem is additional arithmetic work, not a known model blocker |
| `DecodeBuilder::into_array_const` | First: disabled assertion plus padded result | Compile-time evaluator semantics outside runtime-body proof |
| `into_array_const_unwrap`, `Alphabet::new_unwrap` | First: success-domain exact result | Unconditional no-panic claim false by design |
| Alphabet BITCOIN/MONERO/RIPPLE/FLICKR/DEFAULT constants | First: actual bytes/table validity, MONERO/BITCOIN table equality, DEFAULT defined as BITCOIN | MONERO is independently constructed, not a required pointer alias; const model support must be checked |
| `Vec<u8>` encode/decode targets and both `into_vec` | Next: resize, append, truncate, exact failure state | Probe shipped Vec resize/truncate/slice models and allocation domain individually |
| `String` target and encoder `into_string` | Next: append ASCII on success; empty target on callback error | Probe take/into_bytes/from_utf8/unwrap UTF-8 bridge; arbitrary callback no-panic claim false |
| Generic private `encode_into<I>` | Next: finite sequence/clone bridge, actual iteration order | Equal clone/original sequence is not guaranteed by Rust bounds |
| Round trips for mathematical relations and composed calls | Next: uniqueness plus capacities and actual returned prefixes | Open proof work; no external dependency blocker established |
| Mutable `str` target and guard Drop | Later: exact UTF-8 repair, byte borrow, error/unwind behavior | Unsafe and destructor/UTF-8 models require concrete diagnostics; not yet established impossible |
| SmallVec targets; tinyvec ArrayVec/SliceVec/TinyVec targets | Later: container-specific length and mutation/error contracts | External dependency methods need inspected checked contracts; old exclusion insufficient |
| `encode_check_into`, `encode_cb58_into`, `decode_check_into`, `decode_cb58_into`, enabled `onto` | Later: digest and chains plus actual checksum/version/error branches | SHA dependency proof missing; F1–F3 refute stronger intended properties but not actual behavior |
| Error `Display`, Alphabet `Debug`, std::error::Error implementations | Later: formatting requests/results and concrete rendered content when supported | Formatter models and flag/failed-sink behavior must be inspected |
| Derived Copy/Clone/Debug/Eq/PartialEq on release types | Later: exact copies/equality/refinements and formatting | Accepted fork omitted derives under Creusot; no blanket unsupported claim warranted |
| Decode Error `unwrap_const` | Panic behavior only | Deliberately diverges; no total no-panic domain |

Every row is either selected for actual implementation by the extension report,
explicitly pending, or blocked with an individual observed reason. A failed model
probe is evidence about that precise boundary, not proof that all other APIs in
the row are impossible. Helpers, specialized replacements, and generic trait
implementations must retain separate coverage labels.

## Selected implementation scope for the fresh extension run

Selection is not acceptance; the final run inventory and post-run results own
proof status. The selected source is `extensions/crate`, not the unchanged release.

- `wrappers` selects generic input-storing constructors and alphabet setters;
  slice-input disabled codecs through whole-slice/reference target dispatch;
  the decode array target; const-result and success-domain unwrap adapters;
  exact length arithmetic; specialized direct-core vector adapters and allocating
  conveniences; and an actual encode-then-decode runtime client. Vector error
  contracts preserve the old prefix and enlarged length, with tail bytes
  unconstrained. No generic Vec target dispatch theorem is selected.
- `roundtrip` selects both mathematical inverse directions, positional uniqueness,
  unconditional encoder capacity, valid-input decoder capacity, and exclusion of
  numeric buffer errors at full-input-length capacity even for malformed input.
  The reverse decode-then-encode direction has no separate runtime client.
- `defaults` selects the actual numeric-byte BITCOIN, MONERO, RIPPLE, FLICKR and
  DEFAULT definitions and their constructor obligations, plus crate-private
  `from_input` and public `encode`/`decode` default-table bridges. The extra
  runtime `bitcoin()` helper is separate from the constants. Native const
  evaluation is not a formally checked compiler-evaluator theorem.
- `checked_state` selects nine constructor/setter bodies in a separate projection
  containing Disabled, Enabled and CB58 variants, corresponding to both checksum
  features. Exact state preservation/update is independent of the disabled-only
  codec builder type. No enabled codec call or digest implementation is selected.
- Exact-copy manual Clone implementations for Alphabet and the three error
  enums, and generated error PartialEq/DeepModel obligations, are selected with
  their generated refinements. Error Clone copies the entire Copy enum instead
  of calling the insufficiently specified stock char Clone. No exact Debug or
  Display text theorem, nor blanket derived-trait coverage, follows.

Owned/mutable strings, generic iterator encoding, arbitrary AsRef inputs and
arbitrary target implementations, third-party container targets, enabled codec
computation/SHA, formatting semantics, and the deliberate-error panic paths
remain unproved. Individual observed model gaps are recorded in
[the boundary ledger](model-boundaries.md); pending implementation work is not a
claim of model impossibility. Extension wrappers and vector loops do not carry
a blanket termination proof. No complete Rust undefined-behavior theorem is
selected.
