# Verification results

The managed run `default-s00b2z3i` passed on 2026-11-25 for `aarch64-apple-darwin`. It restored and checked the published source, regenerated both Lean model sets byte for byte, clean-built the proof package, and audited 24 named theorems. Before and after fingerprints matched. The staged verification inputs also matched the current checkout at each fingerprinted file. Only `propext`, `Classical.choice`, and `Quot.sound` were permitted by the transitive axiom audit.

The [theorem inventory](theorems.json) maps 12 public methods to proofs of unchanged release bodies. These cover the two constructors and ten explicit encoding selectors. The metrics theorems establish all cached fields for keys and for strings with no quote run longer than 255. The string constructor proof also establishes a checked integer overflow in the model whenever a run of either quote byte reaches 256. The [native finding](../../../verification/findings/TOML-WRITE-001.md) reproduces the public failure when Rust overflow checks are enabled.

Six audited statements cover the two [adapted default selectors](proofs/DefaultSelectionProofs.lean), ordered option-chain equations, and composition with the original constructors. These statements use the disclosed [source patch](patches/default-selection.patch) in a separate extraction. The two unchanged release default bodies still fail extraction. A separate native differential check matched the returned fields of both inputs in all 32 raw key metric states and 524,288 raw string metric states at one fixed decoded string. The native check and source review support the adaptation correspondence.

| Native feature configuration | Unit tests | Doc tests |
| --- | ---: | ---: |
| Default (`std` and `alloc`) | 0 | 2 passed |
| No default features | 0 | 2 passed |
| No default features with `alloc` | 0 | 2 passed |

Both accepted extractions used default features. Rust 1.94.1 ran native checks and nightly 2026-09-17 ran extraction. The accepted tool lock pins unmodified Aeneas `be86ab0f1989d04944292b345b24c435be3ad10a`, unmodified Charon `08d7c9d50144bd84848212c24701253585e90d1f`, and Lean 4.35.0. The preparation and compatibility patches apply to the cargo-proofs CLI. The [recording preflight](evidence/recording-preflight.md) describes API discovery and the recorder and publisher identities. The unchanged-body extraction uses two authored Lean models for standard-library string bytes and emptiness. The adapted extraction applies its patch to a temporary copy of release files.

The [isolated wrapper](../../../scripts/verify-isolated.sh) avoided an unrelated Creusot dependency patch in the parent repository's Cargo configuration. The maintained Cargo.lock resolves the release manifest's dependency constraints without that patch.

The raw run is retained at `.work/runs/default-s00b2z3i` relative to the crate workspace. The [current evidence summary](evidence/recording/summary.json) and [archive descriptor](evidence/recording/archive.json) identify its verified local-only archive under `.work/evidence-archives`. The [earlier 24-theorem acceptance](evidence/extended/summary.json) used the prior CLI pin. The [earlier 15-theorem acceptance](evidence/summary.json) and its [archive descriptor](evidence/archive.json) are retained for their original inputs.

## Remaining coverage

Escaping, delimiter and token output, writer error and effect propagation, numeric formatting, and container serialization remain outside the checked contracts. The [extraction boundaries](extraction-boundaries.md) record the unsupported early returns, recursive trait dictionaries, and omission of literal content in the stock `core::fmt::Arguments` model.

An earlier separate diagnostic built upstream Aeneas HEAD `fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b` and its Charon pin `695be3d6292e988eedd8afcb7a709146a0ff4f01`. Aeneas's tree remained clean. The diagnostic Charon build added an unused Creusot patch record to its Cargo.lock through the ancestor configuration. This run reproduced the writer, default, and standard-library extraction boundaries using the newer tool sources.

| Probe | Local log relative to the crate | Aeneas log SHA-256 |
| --- | --- | --- |
| Generic writer | `.work/core-probe-v35-r2/aeneas.log` | `8d62d2fcf967241259e64675eaff6e3a0b00285c78efb6dc6adb88e3fa8bc9c1` |
| Fixed-token writer | `.work/writer-next/aeneas.log` | `7c06c065c15438a7a8dfff93c83c8e93439dfb10ab45d925acb01b8efab5eadd` |
| Default callbacks | `.work/builders-probe-v35-r3/aeneas.log` | `7d8458d8aef49bec9aed1a307bc2ff766f947406754f8cd566d99050b83e1fa6` |
| Explicit str bodies | `.work/metrics-str-probe-v35/aeneas.log` | `62d8476d7120390f4afeeae7a377f7f44e6f095621ead4df39222b156603d803` |
| Newer generic writer | `.work/core-probe-v36/aeneas.log` | `32be12fb54a3af423478c19e556b63bdbf64d2a9f7efae7e1bc2797b0bf6982f` |
| Newer default callbacks | `.work/defaults-probe-v36/aeneas.log` | `baa2aea81eeaefbcac904951d0a983a6fdf193bb1786c826593685e36a81cf2b` |
| Newer explicit str bodies | `.work/str-probe-v36/aeneas.log` | `85165124d842670fd2432f16c98bc99c84511984fe77687913d25f34d2b2e708` |
