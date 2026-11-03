# Preserved acceptance

The full managed offline verifier passed on 2026-11-03 for profile `default`,
`aarch64-apple-darwin`, default Cargo features, and the original fingerprinted
inputs of `.work/runs/default-33yks7a9`. This records acceptance of those inputs;
future source, proof, configuration or documentation edits require a fresh run.

Two unchanged release bodies are proved: `OptionExt::contains` and
`OptionExt::map_or2` (including the extracted standard `Option::map_or` body).
The third contract, `OptionExt::map_or_else2`, is proved for the disclosed
single-expression direct-match adaptation. Its source correspondence is reviewed,
not formally proved. The original delegated release body's extraction remains
blocked at the standard-library nullary callback; that expected failure was
reproduced separately in the same verification run and no partial Lean was used.
The exact scope, callback premises and trust boundaries are in `specification.md`,
`proofs.toml`, `theorems.json` and the version README. No crate defect was found.

The run regenerated and compared both complete maintained generated Lean files,
ran a local-package clean and standard Lake build, and audited all 12 named
contracts/helpers including the three distinct public mappings. All audits passed;
only `propext`, `Classical.choice` and `Quot.sound` were permitted, with no custom
axioms, `sorryAx`, or native-decision axioms accepted. A separate standard Lean
`#print axioms` check showed the actual dependency set `[propext, Quot.sound]`
for every one of the 12 theorems (no `Classical.choice` dependency). Original and adapted source
hashes were checked before and after extraction. Aeneas and Charon source trees
were unmodified and their binary/source identities matched the tool receipt.

Native evidence is separate: the unchanged release passed three branch tests and
three doctests; the adapted harness passed three branch tests. These tests cover
heterogeneous comparison orientation, owned non-Clone closures and panicking
unselected callbacks. They are not formal proofs.

Pipeline input JSON SHA256, identical before and after:
`333b9c576a8c7369d7d7578f2e7733fb13e7c8b8758a7548313cddad001edceb`.
Audit input JSON SHA256, also identical before and after:
`f04b19a03da0c6541519bf919a9ad17101694152c499956f6e60a5f288b36995`.

`evidence/summary.json` preserves the checked result and artifact digests;
`evidence/archive.json` identifies the complete local-only archive in
`.work/evidence-archives`. That archive is not published or downloadable from a
fresh clone. The archive was verified and its summary matched against original
run bytes using the shared evidence helper. No login, push or publication occurred.

The accepted inputs also include the recording preparation manifest and target-local
CLI scanner fix. All 24 scanner regressions passed, and actual pinned-adapter
discovery matched the three qualified concrete implementation APIs and exact
preconditions. The actual CLI preflight reached the expected commit/push source
prerequisite. These are preparation checks, not a completed recording or upload.
