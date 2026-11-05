# Separate Creusot track for unindent 0.2.4

- The user explicitly requested this Creusot continuation. The parent version's Aeneas-only activation applies to the existing Aeneas track; use only this workspace's `scripts/env.sh` here.
- Keep an independent Cargo workspace and lockfile. Do not modify the immutable release in `../.work/source`, Aeneas proofs, or either verifier's implementation.
- Astra owns independent specification design and contract review; Sol owns runtime adaptation and proof implementation. The primary reviews source identity, assumptions, commands, inventories, evidence and public claims.
- Keep `unindent_bytes`, `do_unindent_bytes`, `unindent` and concrete extension implementations explicit in coverage. Scanner proofs alone do not prove the byte transformation.
- Preserve the release's first-line exception, SPACE/TAB byte counting, initial CRLF handling and interior-CRLF behavior. Do not fix an observed behavior as part of verification.
- Prove successful termination and exact output contents over the complete representable input domain. Never add application-level trusted assumptions or narrow contents to simplify a proof.
- Ledger every additional standard-library model. Character encoding facts and the `String::from_utf8` boundary are assumptions about std; application UTF-8 preservation must be checked.
- Record runtime adaptations and their relationship to the independent specification. Finite native agreement is not a formal equivalence proof with the release.
- Use fresh Coma/Why3find outputs, positive root inventories, all generated target classifications, normal prover results, before/after fingerprints and the shared independent audit. Preserve failed attempts in ignored `.work`.
- Native tests, differential comparisons, body proofs, trait refinements, source correspondence and proofs.rs recording are separate outcomes. Prior Aeneas acceptance remains tied to its archived inputs.
- Source push and proofs.rs publication were authorized earlier in the conversation. Do not log in, contact upstream, file issues, or change unrelated published reports without explicit authorization.
