# Additional bs58 0.5.1 verification results

The extension passed complete fresh verification with **unmodified Creusot
0.13.0 and its standard models**. It proves the selected contracts in an adapted
Rust verification fork, not equivalence to every unchanged release body.

## Established behavior

| Selected operation | Established contract |
| --- | --- |
| Existing four core functions | Alphabet construction, exact Base58 numeric value and leading zeros, capacity/error precedence, successful suffix preservation, and padded fixed-array output. All four were reverified in this integrated run. |
| Constructors, alphabet replacement and default entry points | Exact stored input/alphabet state, with the actual default-table validity bridge. Generic constructor inputs retain their original `AsRef` bound; codec callers specialize to byte slices. |
| Five built-in alphabet constants | Actual BITCOIN, MONERO, RIPPLE, FLICKR and DEFAULT initializers pass. MONERO has Bitcoin table values; no pointer identity is claimed. |
| Slice/decoder-array targets and mutable-reference forwarding | The selected concrete implementations propagate the checked callback's result and byte mutations; body and generated trait-refinement goals pass. Arbitrary upstream target implementations are not covered by an unconditional output theorem. |
| Slice `onto` / decoder `onto_array` | Complete core success/error relations through the selected callback dispatch, including the unused successful suffix. |
| Specialized vector `onto_vec` and `into_vec` | Under the stock allocation model and stated machine-addition bounds, encoding succeeds and appends the exact output. Decoding appends the exact payload on success and cannot return `BufferTooSmall`, including for malformed input. Errors preserve the old prefix but retain the enlarged, partially modified tail. These are direct-core specializations, not proofs of generic Vec target dispatch. |
| Length bounds | The exact expression `h(n)=n+(n+1)/2` is sufficient for encoding; an input-length buffer suffices for decoding valid text and cannot incur a numeric capacity error for arbitrary text. Machine-overflow obligations remain explicit. |
| Array/alphabet unwrap conveniences | Exact successful results under their success-domain premises. Error inputs deliberately panic. Compiler constant-evaluation semantics are not formally certified. |
| Clone / error equality | Exact copies for Alphabet and the three default-feature core error enums; the error PartialEq bodies and refinements pass. No exact Debug/Display-output claim follows. |
| Full-feature checksum-state projection | Nine constructor/alphabet/mode/version setter bodies preserve the specified fields. This separate state-only projection does not compute digests or compose enabled-checksum codec execution. |
| Round trips | Both mathematical relation directions include leading-zero uniqueness. The actual `encode_decode_roundtrip` client also proves the allocating encode-to-decode result equals the input. The reverse direction is a relation theorem, not a second runtime client. |

Vector guarantees concern contents and logical length. Capacity, pointer identity,
allocation-call sequences, physical allocation-domain limits, capacity-limit
panics and resource failures are outside the abstract allocation model. The
additional runtime wrappers do not have a blanket total-termination claim;
arbitrary callback termination is not assumed. The original core termination
checks and the logic lemmas' decreasing arguments are separate obligations.

## Accepted formal evidence

The authoritative run is `.work/extensions/formal-vkijxx6d`:

- Fresh Cargo target directory and generated Coma; compile, prove and audit exits
  are all **0**.
- The exact frozen inventory contains **135 targets**: 126 bodies, helpers and
  constant initializers, plus **9 trait refinements**. Target counts are not
  public-API counts.
- **242 original roots** independently reconstructed and matched exactly to the
  nonempty proof sessions; **612 SMT-proved leaves**.
- **123 computational closures**, each replayed for its exact original goal with
  standard Why3 and zero residual tasks.
- Every target process succeeded; all proof trees closed; before/after source,
  configuration, model and executable fingerprints match.

See the [summary](evidence/summary.json), [complete target/root inventory](evidence/goal-inventory.json),
[compact replay records](evidence/computed-roots-replay.json), and
[independent Astra review](final-review.md). Specifications were designed by
Astra; implementation and proof work used Sol agents. The same nine runtime
source files were used by the accepted native comparison, as checked in the
[cross-run audit](evidence/cross-run-source-audit.json).

Creusot remains at clean official revision
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`; executable and standard-model hashes
match the existing [tool identity](../toolchain.json). The user's installed
Why3/Why3find opam switch was reused without modification. No application
algorithm, arithmetic lemma, or missing dependency contract was assumed.

The extension-local evidence checker adds recognition of explicit `goal refines`
declarations and conservative handling of Why3's printed apostrophe identifiers.
It preserves exact original namespace selection, an injective printed-name map,
positive root identity and zero residual tasks. Eight synthetic and six real
Why3 positive/negative controls were independently checked. This is a local
auditor change; no verifier, transformation, driver, solver or standard model was
patched. The original core checker remains unchanged.

The earlier `formal-f04h1fbu` prover run succeeded but failed its original audit
gate; the next attempt was stopped while identifier handling was corrected.
Neither is acceptance evidence. Their raw output remains retained.

## Native correspondence observations

The strict run `.work/extensions/native-7eq5hgpv` passed with unchanged input
fingerprints and all 24 pinned registry-release files checked before and after:

- 82,944 slice-wrapper comparisons;
- 80,819 array-wrapper comparisons, including successful unwrap calls;
- 43,200 vector-wrapper comparisons;
- 2,560 built-in-alphabet codec and 512 default-frontend comparisons;
- 3,600 composed runtime round trips and nine maximum-length examples.

The comparisons inspect all buffer bytes on both `Ok` and `Err`; vector equality
compares byte contents and logical length, not capacity or allocation identity.
Three additional witnesses illustrate custom-target, repeated-`AsRef`, and
String-error-state boundaries. They are **not bugs**. These finite observations
do not constitute formal release equivalence. See the
[native summary](evidence/native-summary.json) and [source correspondence](../../extensions/correspondence.md).

## Findings and remaining functions

No new bs58 defect was established in this extension. The existing three
[checksum findings](../findings/README.md) are retained; their affected checksum
computations are not certified by these proofs.

The remaining boundaries have individual evidence rather than only old scope
exclusions:

- Arbitrary generic iterator encoding requires a checked finite, identical
  clone/original sequence law not implied by the Rust bounds. Arbitrary custom
  targets and unstable `AsRef` implementations likewise need explicit semantics.
- SHA dependency calls have no applicable installed contracts and generate false
  call preconditions; enabled-checksum codec computation remains unproved.
- String/UTF-8 conversion, mutable bytes, error-position observers and an ASCII
  byte bridge are missing from the installed models. Exact unsafe string repair
  and owned-string byte results remain unproved.
- Formatter models provide no observable output/result relation sufficient for
  exact formatting guarantees.
- SmallVec and tinyvec operations have individually observed missing resize,
  truncate, indexing, spare-buffer and length-update contracts.
- Unconditional no-panic claims for intentionally panicking unwrap functions
  are false by design. Whole-crate UB freedom and formal release equivalence
  are not established.

The [stock-model ledger](model-boundaries.md) and
[optional-container/generic-iterator diagnostics](optional-boundaries.md) link
the actual callees and retained probes. They do not claim these tasks are
impossible with additional checked dependency/application work.

## Reproduction and archive

Use [the extension guide](../../extensions/README.md). Raw output, generated Coma,
proof trees, source/model snapshots, checker controls and native logs are retained
in the [archive descriptor](evidence/archive.json). The archive is local-only;
the checksum is not a public download URL. Public source and compact evidence
support a fresh reproduction. Publication recording and receipts are separate
from this formal acceptance.

The subsequent standard recording
`ec72449d-897f-42a7-8b97-d04dead9eab0` also succeeded with the unmodified installed
cargo-proofs 0.4.1. Its complete captured formal prover run has 135 targets, 242
reconstructed roots and 750 positive solver leaves. Its source-bound SARIF
contains 21 fork API entries and 65 passing root results. The
[recording summary](../../extensions/publication/recorded-run-summary.json) and
[independent native goal audit](../../extensions/publication/native-goal-audit.json)
retain those distinct scopes. The [reporting notes](reporting-notes.md) explain
why generic builder methods and generated methods/refinements do not all appear
as separate API entries; they remain covered by the full proof inventories.

[Report 19, revision 2](https://proofs.rs/report/19) publishes the expanded scope.
Anonymous readback matched the submitted content; four earlier claim IDs and all
three findings were preserved. The
[publication receipt](../../extensions/publication/publication-receipt.json)
records the source, execution record and exact publication payload digest.
