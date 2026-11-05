# Creusot verification plan

## Identity and source

- Subject: crates.io `unindent` 0.2.4, selected in the original request.
- Archive SHA-256: `7264e107f553ccae879d21fbea1d6724ac785e8c3bfc762137959b5802826ef3`.
- Registry resolution: 2026-11-03, retained in `../../verification/source-identity.json`.
- Release VCS metadata: `dtolnay/indoc`, commit `f5934e4a743c455e4cfd283d827bf4c36ff6017f`, path `unindent`.
- Authoritative executable source: `../../.work/source`, checked against the complete inventory in `../../source.lock.json`.
- The annotated implementation is a verification adaptation. An explicit function/source map and native comparison must accompany the final evidence; no all-input release equivalence is assumed.

## Build and execution surface

The release has no application dependencies, optional features, build script,
unsafe application blocks, async operations or IO. Verification adds pinned
`creusot-std` annotations and local proof/model modules. The native target for this
attempt is Linux `x86_64-unknown-linux-gnu`; other targets and MSRV compatibility
are not established by this run.

Use frozen Creusot 0.13, its `nightly-2026-06-22` extraction compiler, Why3 and
Why3find through `scripts/env.sh`. The installed native compiler is selected
separately. Capture actual runtime paths, versions and hashes, including resolved
Cargo dependency sources rather than inferring them from a manifest patch.
Do not modify either verifier or mix the Aeneas activation into this process.

## Intended contracts

| Target | Observable guarantee | Required composition |
| --- | --- | --- |
| `common_margin` | Exact attained minimum over later nonblank lines, or zero for an empty eligible set | Relate candidates to independent LF decomposition |
| `do_unindent_bytes` | Terminates without modeled panic; exact flagged transformation `U_p` and output length bound | Minimum, byte selection, output order and independent specification bridge |
| `unindent_bytes` | Exact `U_false` for arbitrary bytes, including invalid UTF-8 | Private byte-core contract |
| `unindent` and private string wrapper | Exact output bytes and successful UTF-8 conversion | Checked ASCII-erasure preservation plus reviewed std conversion model |
| Concrete `Unindent` implementations | Exact delegation with the appropriate byte/string contents | Body and generated refinement/law obligations |
| Generic reference implementation | Delegation only; underlying user implementation controls success and contents | Preserve arbitrary legal trait implementations |

First-line exceptions, trailing and consecutive empty lines, SPACE/TAB counting,
initial CRLF stripping, interior CR bytes, empty input and arbitrary non-ASCII
bytes must retain the release behavior. A lower bound on indentation alone is
insufficient; the minimum must be attained whenever eligible lines exist.

## Trust and correspondence

Application computations must have checked bodies. Additional models are limited
to the explicit standard-library boundaries in `assumptions.md`. The exact byte
contract must be connected to the independent mathematical specification, not
only to a ghost copy of the runtime loop. UTF-8 validity of application output
must follow from checked preservation lemmas and checked byte-core properties.

Prefer the release's runtime code where tool support permits it. Preserve the
actual original-source failure when a boundary is unsupported. The indexed
implementation is a permitted source adaptation; record each changed operation,
its reason, and the observations covered by differential tests. Finite comparisons
and source review do not become formal all-input equivalence proofs.

## Milestones and evidence

1. Probe the actual original pipeline and identify its first unsupported boundary.
2. Prove the complete byte transformation with exact minimum/output contracts.
3. Prove checked UTF-8 preservation and the string/concrete wrapper contracts.
4. Freeze inputs; compile fresh Coma; classify every generated target; close all
   selected positive root goals using standard Why3find; reconstruct inventories
   independently and compare before/after source/tool fingerprints.
5. Run native and differential checks separately, then record precise source scope,
   remaining obligations, assumptions and publication outcome.

Reassess feasibility at each milestone and after substantial unsuccessful proof
work. There is no user-imposed time or token cap. A blocker must remain explicit;
do not drop a contract or application proof to obtain a successful count. Run IDs,
goal counts and outcomes belong in the post-run results page, not this plan.
