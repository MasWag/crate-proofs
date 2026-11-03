# bs58 0.5.1 Creusot workspace

- This independent workspace implements the user's Creusot verification request. The parent version's unchanged-source restrictions and commands describe its historical Aeneas profile; preserve that profile and its evidence.
- Keep Creusot, its standard-library models and proof infrastructure unmodified. Record the exact upstream revision and clean source identity before and after proof.
- Application annotations and faithful Rust adaptations are permitted for this trial. Preserve the original release under the parent `source.lock.json`; inventory executable changes and distinguish reviewed correspondence from formally proved equivalence.
- Specification design belongs to Astra; proof implementation belongs to Sol, as requested by the user. Preserve independent intended contracts, including errors and boundary cases. Do not trust application algorithms or count helper-only proofs as codec verification.
- Keep this Cargo workspace and its lockfile independent. Keep raw run output and build products in ignored `.work/`; keep compact results, coverage, correspondence and findings under `verification/`.
- Follow the repository's Creusot verification and findings skills. Record native tests separately from positive, complete formal proof obligations; retain failed probes and unproved scope.
