# unindent 0.2.4 verification

- Use the repository Aeneas skill and managed setup/verify wrappers. Do not activate Creusot.
- The subject is the latest non-yanked registry release resolved on 2026-11-03, pinned by `source.lock.json`. Restore it into `.work/source`; never edit that immutable source.
- Aeneas itself must remain unchanged. Pin official source and binary identities and reject any Aeneas patch. Clearly distinguish any exploratory Rust adaptation from the release implementation; tests alone do not prove equivalence.
- Keep `unindent_bytes` and `unindent` explicitly in the coverage ledger. Private helper proofs do not establish either public algorithm.
- The Astra specification agent owns independent specification design; the Sol implementation agent owns extraction and proof implementation. A separate report writer drafts prose, Astra reviews correctness, and the primary reviews final claims and evidence.
- Require successful execution plus exact output in functional contracts. Preserve arbitrary byte inputs and UTF-8 obligations; do not narrow contracts to fit a tool limitation.
- Preserve failed extraction diagnostics in ignored `.work` and document blockers separately from crate findings. Never accept partial generated output or application axioms.
- Native checks, checked Lean theorems, release correspondence, CLI recording and proofs.rs publication are separate outcomes.
- The user requested proofs.rs publication. Do not infer authorization to contact upstream or file issues. Source pushes require explicit authorization.
