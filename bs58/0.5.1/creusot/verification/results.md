# bs58 0.5.1: Creusot verification results

The four selected Base58 core functions passed functional-correctness, indexing,
arithmetic and termination verification with **unmodified Creusot 0.13.0**.
The result applies to the documented Rust proof adaptation on x86_64 Linux, under
Creusot's shipped models. It does not certify every API in the published crate.

## Established behavior

| Function | Checked contract |
| --- | --- |
| `Alphabet::new` | For any 58-byte array, constructs exact forward/inverse tables for distinct ASCII symbols, or returns the first non-ASCII/duplicate error with the specified indices and character. It has no validity precondition. |
| `encode_into` | For any byte slice and valid alphabet, preserves its base-256 numeric value in base 58 and its exact leading-zero count. Returns the complete encoded prefix exactly when the buffer fits; otherwise returns `BufferTooSmall`. A successful call preserves every byte after its returned prefix. |
| `decode_into` | For any input bytes and valid alphabet, returns the corresponding base-256 prefix with exact leading zeros when it fits. Character errors, their indices and capacity-dependent precedence are checked. A successful call preserves the unused buffer suffix. |
| `decode_into_const` | The same decoding/error relation for capacity `N`; success returns the decoded prefix followed by zeros to fill the array. |

All four functions include checked termination requirements. Bounds and overflow
conditions are discharged over their contract domains. The codec alphabet premise
is explicit; successful `Alphabet::new` establishes the required table laws.
No buffer rollback guarantee is made on error. The independent mathematical
definitions and exact premises are in [the specification](specification.md).

## Accepted formal run

The authoritative run is `.work/creusot-run-8KtCLWaA`:

- Fresh Cargo target directory and fresh generated Coma; compilation exit **0**.
- All **56** generated targets invoked in separate standard, cache-disabled
  Why3find processes; all **56** process exits were **0**.
- **72** original root obligations independently reconstructed and matched to the
  complete proof-tree inventory.
- **542** solver-proved leaves and **16** computationally closed roots. Each of
  those 16 roots was separately replayed through standard Why3 `compute_specified`:
  the original selected goal existed, and transformation left zero residual goals.
- No unresolved trees. Source, specification, checker, configuration and relevant
  tool fingerprints matched before and after verification.

The [machine summary](evidence/summary.json), [goal inventory](evidence/goal-inventory.json)
and [independent Astra review](review-notes.md) identify the accepted evidence.
Earlier interrupted or incomplete probes are not acceptance evidence.

## Source correspondence and trust

The reference is the unchanged crates.io **bs58 0.5.1** archive, SHA-256
`bf88ba1141d185c399bee5288d850d63b8369520c1eafc32a0430b5b6c287bf4`.
The proof crate is named `bs58_creusot`. Its adaptations include slice specialization
of the generic encoder, index loops and explicit reversal, and equivalent bounded
integer multiplication/division/remainder expressions. See [correspondence](../correspondence.md).

The fixed-array decoder shares one computation body between a native `const fn`
and an ordinary function in the Creusot build, where checked ghost calls are legal.
The body computation is verified; Rust's compile-time evaluator is not formally
verified here. Native compile-time calls were tested separately.

The relationship to the release is supported by source review and finite native
comparisons, **not a formal release-to-fork equivalence theorem**. The encoder proof
does not cover arbitrary `Clone + IntoIterator` implementations or checksum chains.
Public builders, allocation/container targets, unsafe UTF-8 string handling,
derived traits and checksum/cryptographic implementations remain outside this proof.
These core proofs also do not establish cross-tool composition with the prior
Aeneas builder proofs.

Creusot and its Rust standard-library models remained at clean official commit
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`. The four installed prelude files matched
fresh output from that revision's unmodified generator. No application algorithm
was marked trusted or supplied as an unchecked assumption. The Rust compiler,
Creusot translation/models, Why3 transformations and SMT solvers are trusted
infrastructure; resource exhaustion is outside the model.

The [tool identity](toolchain.json) records executable/model hashes. Why3 and
Why3find were reused read-only from the user's existing opam switch. Specifications
were designed with Astra; proof implementation used Sol and Sol 6.1; Astra performed
the independent correctness/evidence review.

## Native observations and findings

The strict final native run `.work/native-final-ha3o_dyw` exited **0** with unchanged
input fingerprints. It checked all 24 registry-release files against the source
lock both before and after execution. It compared **145,388 paired codec cases**,
**120,000 fixed-array results**, and **348 constructor outcomes**, including complete
buffers on errors. Native constant evaluation exercised an empty array and leading
zeros with right padding, including comparison with the upstream const API.
These are finite observations, separate from the formal contracts.

The original release's initial native test run with `check` and `cb58` also passed
54 tests, including 38 documentation tests; its log is retained in the evidence
archive. It is a separate baseline observation.

The [findings](findings/README.md) retain three previously observed discrepancies,
independently reproduced in this trial:

1. F1: checksum-only input can satisfy a requested version byte.
2. F2: checked decoding writes checksum bytes beyond its returned payload length.
3. F3: `InvalidChecksum` fields disagree with their documented meanings.

They are not three new unchecked-core defects. Checksum paths are outside the
formal scope; no release fix or upstream issue filing was performed.

## Reproduction and evidence availability

From this workspace, prepare the [pinned environment](toolchain-setup.md), then run:

```bash
source scripts/env.sh
bash scripts/verify.sh
python3 scripts/check-native.py --offline
```

Offline native execution requires its locked dependencies to be cached. The recorded
native run used a separately selected Cargo home and the existing Rust 1.94.1 installation;
the native checker accepts explicit home/toolchain options and records them.

The [archive descriptor](evidence/archive.json) identifies retained source snapshots,
generated Coma, proof trees, logs and audit records. The archive is local-only under
ignored `.work/`; its checksum is not a public download link. A fresh clone can rerun
the proof after tool setup. Packaging these records does not rerun verification.
