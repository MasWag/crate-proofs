# Publication recorder fixture

This independent Cargo workspace gives the verification fork the registry subject
identity `bs58` / `0.5.1` required by proofs.rs. It is a verification fork, not the
registry distribution. See [source correspondence](../../correspondence.md), the original `../../crate/`, and the report limitations for release
correspondence and excluded public wrappers.

The three specification/helper files in `crate/src/` are byte-for-byte copies of
the accepted proof crate sources. `lib.rs` expands the Creusot instance of the
fixed-array decoder macro into a direct function for the recorder scanner; its
function body and annotations are unchanged. Only the publication fixture omits
that function's native `const` qualifier. `source-transformation.json` records the
exact transformation and source hashes. The package manifest uses exact registry
`creusot-std = "=0.13.0"` rather than an external local path, so a detached source
snapshot contains all local Cargo packages. `registry-source-comparison.json`
records that all 127 Rust source files in creusot-std, creusot-std-proc and
pearlite-syn match the pinned, unmodified official Creusot commit.

The local Why3find configuration has no preprocessing tactic and uses direct
Z3/CVC5 proof search followed by `split_vc`. This avoids zero-child
`compute_specified` proof trees that cargo-proofs 0.4.1 cannot import. This changes proof search without changing contracts, verifier, models or solver
semantics.
A fresh recorder run is separate evidence from the original complete proof run.

After publishing the source commit, activate the pinned environment and run the
unmodified standard recorder from this directory's `crate/`:

```sh
source /absolute/path/to/creusot/scripts/env.sh
export TMPDIR=/absolute/path/to/creusot/.work/publication-tmp
mkdir -p "$TMPDIR"
/home/lab8/mwaga/.cargo/bin/cargo-proofs proofs run -- \
  cargo creusot --no-cache --span-mode absolute \
  --why3find-arg=-j --why3find-arg=2
```

The original accepted sources, contracts, run and evidence archive are preserved.
Only a successful fresh standard recorder result can supply publication claims.
The standard Creusot importer claims panic-contract verification; the narrative
functional guarantees refer to the separately identified complete proof evidence.
