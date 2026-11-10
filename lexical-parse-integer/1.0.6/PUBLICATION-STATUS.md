# Publication status

This is a local publication draft. The proof package has not been committed, recorded with cargo-proofs, or published.

The first proofs.rs import attempt failed with `unsupported_rustdoc_format` (job `7a98ec24-51a4-48ca-9be4-718ff3f63a3a`): the crates.io 1.0.6 rustdoc JSON uses format version 56, while that service build accepted versions 60 and 61. The compatibility change merged as proofs-rs PR #98 at commit `3746712` and its production workflow run `42612554819` is queued as of 2026-11-09. A retry under the previous deployment (job `f03b3978-c4c2-43cc-a8ac-192631c1519d`) still failed with `unsupported_rustdoc_format`. Public API catalogue preparation and recording must be retried after deployment.

`proofs.toml` proposes 13 direct Options API mappings and includes two native findings. The ten supporting managed Aeneas/Lean profiles and evidence are under `aeneas/profiles/`. The flat Options Lean package is under `proofs/`. The feature-gated `from_radix` theorem and adapted parser contracts are supporting evidence; they are not mapped to public parser APIs in this draft.

Before publication, verify the live catalogue paths, review and commit this package on a dedicated source branch, run the official cargo-proofs recorder from that exact commit, inspect its claims, then submit the report.
