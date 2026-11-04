# Standard recording fixture

This independent workspace is named `bs58` version `0.5.1` for proofs.rs. It is
the disclosed verification fork, not the crates.io source distribution.

`source-transformation.json` pins its correspondence to the accepted extension:
eight Rust files are byte-identical; the root file expands the fixed-array
decoder macro into the same ordinary verification function. The computational
body and all annotations are unchanged. The original native const decoder remains
in the accepted application workspace.

The fixture uses exact registry `creusot-std = "=0.13.0"`; all 127 Rust files of
the standard crate and its proc/Pearlite dependencies were rechecked against the
pinned official source. Registry Cargo manifest normalization is not full package
equivalence. The verifier, installed prelude, models and solvers are unchanged.

Its Why3find configuration uses direct SMT search and split_vc without compute
preprocessing, so every imported proof tree must have a positive solver leaf.
Preparing this fixture does not itself establish a recording result.

After committing and pushing the source, start in the Creusot workspace:

```sh
source scripts/env.sh
export TMPDIR="$PWD/.work/extensions/publication-tmp"
mkdir -p "$TMPDIR"
cd extensions/publication/crate
cargo proofs run -- cargo creusot --no-cache --span-mode absolute \
  --why3find-arg=-j --why3find-arg=2
```

Use the installed unmodified cargo-proofs 0.4.1 and a writable TMPDIR under the
ignored Creusot `.work/` directory. The standard recorder checks a fresh detached
Git snapshot and embeds real logs/proof trees in SARIF. Its Creusot adapter records
panic-contract API entries; the full functional and refinement evidence is the
separate accepted extension audit. The successful fresh recording is described in
[`recorded-run-summary.json`](recorded-run-summary.json): 21 fork API contracts
and 65 passing imported root results. The global recorder and verifier both
exited successfully. The standard importer scope is separate from the full
functional and refinement audit. The complete captured formal run also passes the
independent [goal audit](native-goal-audit.json): 135 targets and 242 roots with
positive solver trees. Generic builder methods and generated equality/refinement
functions appear in the complete proof inventories even when the standard
importer supplies no separate API binding. Publication is recorded separately.
