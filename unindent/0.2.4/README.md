# unindent 0.2.4

This workspace investigates the published unindent release with unchanged Aeneas.
The registry index resolved on 2026-11-03 ends at non-yanked version 0.2.4. Its
archive SHA-256 is
`7264e107f553ccae879d21fbea1d6724ac785e8c3bfc762137959b5802826ef3`.
`source.lock.json` pins the complete release inventory; `.work/source` is restored
from that archive. The outer Cargo workspace preserves the release build surface.

The independent [specification](aeneas/profiles/default/specification.md) lists
public operations and core algorithms separately from private helpers. Read the
profile's [results](aeneas/profiles/default/results.md) for checked scope and remaining extraction/proof obligations.
Specification text and successful extraction alone are not correctness proofs.

Use `scripts/setup.sh` and `scripts/verify.sh` for the managed profile once its
configuration is complete. Raw experiments and execution records remain in ignored
`.work/`. Publication on proofs.rs is a separate recorded operation.

The separate `adapted` profile contains an explicit Rust refactoring and proofs of
two scanner helpers. Its full byte core and formal equivalence to the release are
unproved; it does not enlarge the default report's public API coverage.
