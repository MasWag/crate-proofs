# Verification results

The frozen managed run `default-cuqijm4d` passed on aarch64-apple-darwin. It regenerated and compared the selected model, freshly built the local Lean package, audited all 12 named theorems, reran source/adaptation/boundary checks, and produced identical before/after input fingerprints. [The acceptance summary](evidence/summary.json) records the exact run and log digests. Earlier failed runs remain retained and are not acceptance evidence.

The selected input is a derived, trait-bound-erased facade harness. Its six generated functions have six exact forwarding equalities and six conditional total-success transfer theorems in [Proofs.lean](proofs/Proofs.lean). The latter require the supplied trait call to succeed and already satisfy the chosen output relation. Writer equality includes the mutable-borrow backward function. The six recorded API mappings name harness functions, not release APIs; the equality lemmas are checked auxiliary theorems.

The harness copies the six release function definitions verbatim and retains their needed method signatures, while weakening trait and associated-type bounds. [The adaptation record](../../../verification/facade/adaptation.json) and `scripts/check-facade-adaptation.py` document and check source correspondence. They do not prove equivalence to the release dictionaries. The unchanged facade extraction generates Lean with unresolved float cast fields and fails to compile; `scripts/check-original-facade-blocker.py` reproduces that boundary.

| Requested operation | Status and boundary |
| --- | --- |
| Integer complete and partial parse | Open. The selected default-feature complete and partial `u32` parse call graphs reach Charon but Aeneas reports unsupported early returns in loops. |
| Release integer write | Open. The selected default-feature `u32` call graph reaches Charon but Aeneas reports `Unreachable` in lexical-util's numeric code. |
| Float complete and partial parse | Open. The selected default-feature complete and partial `f64` parse call graphs reach Charon but Aeneas reports an unsupported break to an outer loop. |
| Float write, roundtrip and shortest formatting | Open. The selected default-feature `f64` call graph reaches Charon but Aeneas reports an internal error in `write_special`. |
| Concrete trait dispatch and release facade equivalence | Open; the adapted dictionary has no built-in numeric implementations and no formal bridge to the release. |
| Options, custom formats, optional features and other types | Open; the six probes are representative boundaries, not exhaustive extraction results. |

`scripts/check-core-blockers.py` reruns these six probes and checks their diagnostics. These extraction failures do not imply incorrect Rust behavior or impossibility of a proof. Aeneas and Charon are unmodified. See [the specification](../../../verification/SPEC.md) for the independent numerical obligations and fuller coverage ledger.

Native execution is separate from formal proof. The accepted run separately passed the default native suite: 5 integration tests and 30 doctests. Separately, the release behavior workspace reproduces two custom-format integer parser observations, with issue-ready drafts and evidence linked from [findings](../../../verification/findings/README.md). LC-001 reproduces the known upstream issue #225 symptom; no novelty claim or upstream filing is made for LC-002. The pinned proofs-rs CLI does not accept `report.findings`, so these drafts remain separate rather than being inserted into an invalid configuration.

## Reproduce the accepted local run

From the repository root, with the pinned offline caches already prepared, the exact command was:

```sh
AENEAS_LAKE_CACHE=$PWD/lexical-parse-integer/1.0.6/.work/build/sign/aarch64-apple-darwin/proofs/.lake/packages bash lexical-core/1.0.6/scripts/verify.sh --profile default --offline
```

The wrapper sets `CARGO_HOME` to the version-local `.work/cargo-home`. Managed setup selected `.work/tools/b2f666ef0902d4b779bbbb0f81e7b9b90d1fe3f630dda0dfe475b7e35c1acd4e` and checked its locked source trees and binary identities. The dependency donor above is local to this checkout; setup validates its pinned revisions and clean sources before reuse. Tools were Rust 1.94.1 for native checks, nightly-2026-09-17 for extraction, and Lean 4.35.0. Aeneas and Charon had no source patches. The inherited Cargo configuration is checked by `verification/execution-config.json`; no Creusot environment was activated.

- Result: `.work/runs/default-cuqijm4d/result.json`, SHA-256 `a54ddf15cd0516568fa1b530c265d03171bdec716830e37a2e04418ccc425103`.
- Identical before/after fingerprints: `130b98866b4360bddd2d4ee344d52f43cf48383cdf8f753a08da4cf4aa16a593`.
- Transitive axiom audits allow only `propext`, `Classical.choice`, and `Quot.sound`; all configured named theorems passed.

Raw LLBC, generated files, build logs and audit logs remain local-only under the run directories. These local results establish the stated adapted/conditional scopes, not whole-crate verification, formal release equivalence, CLI proof recording or publication.
