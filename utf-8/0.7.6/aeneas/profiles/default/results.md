# Verification results and coverage

The final managed run `.work/runs/default-lc40z08m` passed extraction, Lean build,
and the named-theorem and transitive-axiom audit for the eight contracts below.
The run used the unchanged `utf-8` 0.7.6 release on `aarch64-apple-darwin`.
Native tests passed separately: five integration tests and one documentation
test. These tests are not formal proofs.

| Operation | Checked scope |
| --- | --- |
| `Incomplete::empty` | Total successful model return with a zero buffer and zero length. |
| `Incomplete::is_empty` | Total successful model return, true exactly when the stored length is zero, for every represented state. |
| `Incomplete::new` | Total successful model return for inputs of length at most four, preserving the input, zero-padding the remaining buffer, and recording its length. |
| `Incomplete::take_buffer` (private) | For stored length at most four, returns that prefix, preserves the buffer, and resets the length. |
| `LossyDecoder::new` | Preserves the callback and initializes an empty buffer. |
| `BufReadDecoder::new` | Preserves the reader, initializes an empty buffer and zero consumption. |
| `Incomplete::clone` | Preserves the entire represented state. |
| `DecodeError::clone` | Preserves the variant and all represented fields. |

These are seven public API claims and one private helper theorem. The proof
concerns translated model execution and depends on the Rust translation and
models; it is not a complete Rust memory-safety or Rust-to-Lean correspondence
proof. Aeneas and Charon are unpatched. The pinned proofs-rs CLI has a local
preparation patch, recorded in `toolchain.lock.json`.

## Core algorithms and remaining work

No correctness proof is claimed for `decode`, `try_complete`, its offsets
helper, `LossyDecoder::feed`, or `BufReadDecoder::next_strict`. The boundary
probe run `.work/boundary-probes/run-dwqnscon/` records these blockers:

| Area | Extraction boundary or remaining obligation |
| --- | --- |
| `decode` and completion offsets | Default extraction leaves external UTF-8 validation, unchecked conversion and error projections as forbidden axioms; completion also reaches an external `Option` branch. Selecting standard-library bodies encounters an inconsistent projection and an unsupported `&[u8]` to `&str` transmute. |
| `LossyDecoder::feed` | Nested borrows in the consumer prevent extraction. |
| `BufReadDecoder::next_strict` | Extraction encounters an internal error. |
| Streaming and lossy consumers | Whole-stream behavior, callback and I/O boundaries, and transient-error recovery remain unproved. |
| Formatting and error accessors | Not covered by the selected proofs. |

The inherited `DecodeError::source` wrapper compiled and returned `None` in
the model, but audit of `.work/runs/default-y4gfhj08/audit/audit1.log` found
a backend `core.fmt.Formatter` axiom transitively through the dynamic error
return type. It is therefore excluded from accepted claims. Alternative
boolean-observer extraction probes also failed; see the local probe evidence.

## Release method ledger

These 23 release-authored or derive-generated method bodies are distinct from
the inherited standard `Error::source`; Copy implementations are markers.
Probe results are local-only in `.work/boundary-probes/methods-8r0owcfb/results.json`.
Successful extraction alone is not a correctness proof.

| Method | Status |
| --- | --- |
| `decode` | Unproved; UTF-8 validation and string-conversion extraction boundaries above. |
| `Incomplete::empty` | Checked. |
| `Incomplete::is_empty` | Checked. |
| `Incomplete::new` | Checked for length at most four. |
| `Incomplete::try_complete` | Unproved; validation, conversion and `Option` boundaries. |
| `Incomplete::take_buffer` | Checked private helper for length at most four. |
| `Incomplete::try_complete_offsets` | Unproved; validation and error projections remain external. |
| `LossyDecoder::new` | Checked. |
| `LossyDecoder::feed` | Unproved; nested borrow extraction failure. |
| `LossyDecoder::drop` | Unproved; generated replacement literal fails Lean parsing ([tool record](../../../verification/findings/UTF8-TOOL-001.md)). |
| `BufReadDecoder::new` | Checked. |
| `BufReadDecoder::next_strict` | Unproved; extraction internal error. |
| `BufReadDecoder::next_lossy` | Unproved; `next_strict` and closure extraction fail. |
| `BufReadDecoder::read_to_string_lossy` | Unproved; those boundaries and string operations remain. |
| `BufReadDecoderError::lossy` | Unproved; I/O error representation and replacement literal boundaries. |
| `BufReadDecoderError::source` | Unproved; dynamic and I/O error representation remain external. |
| `DecodeError::Display::fmt` | Unproved; slice Debug and formatter models are boundaries. |
| `BufReadDecoderError::Display::fmt` | Unproved; formatter and I/O Display models are boundaries. |
| `Incomplete::Debug::fmt` | Generated model compiled, but formatter model erases field output. |
| `DecodeError::Debug::fmt` | Unproved; probe aborts with `Invalid_argument: option is None`. |
| `BufReadDecoderError::Debug::fmt` | Unproved; probe aborts with `Invalid_argument: option is None`. |
| `Incomplete::clone` | Checked. |
| `DecodeError::clone` | Checked. |
| Inherited `DecodeError::source` | Not a release-authored body; wrapper audit failed on the transitive formatter axiom described above. |

The checked storage lemmas do not establish UTF-8 algorithm correctness. A
classifier-only Rust refactor would also need a proof of the UTF-8 language and
a correspondence bridge to the release implementation. The separate
`core_adapted` profile factors a descriptor-based transition, but its relation
to the original implementation is not formally proved. Source adaptation and
release equivalence are separate from closing function goals.

## Findings and provenance

Native reproductions document two behavior/specification questions, not two
confirmed violations of documented contracts: [UTF8-001](../../../verification/findings/UTF8-001.md)
and [UTF8-002](../../../verification/findings/UTF8-002.md). Neither establishes
a failure of the usual decoder-produced state or standard `BufReader`, respectively.

The registry index identified 0.7.6 as the latest version; the crates.io API
request returned HTTP 403. The release archive checksum is
`09cc8ee72d2a9becf2f2febe0205bbed8fc6615b7cb429ad062dc7b7ddd036a9`, and its
recorded VCS revision is `9b4165786edaea2ef9cf48f75756537eacf7f20d`.
`source.lock.json` records individual release file hashes. A preexisting
ancestor `.cargo/config.toml`, SHA-256
`06f72117aa7d62643bcc985492d51243b06d64f8c28b1d766d35b3597f837bed`,
was an execution input; its `creusot-std` patch was unused in the native run.
It is outside the managed fingerprint. No global configuration was changed.
The ancestor configuration hash was checked before and after the final run and
was unchanged. Run and probe artifacts under `.work` are ignored, local-only
evidence; the paths above are not public download links.
