# Original delegated map_or_else2 with Creusot

This independent workspace checks the released `Option<T>` implementation of
`OptionExt::map_or_else2`, retaining `self.map_or_else(default, f)` and its runtime
signature. A strict source checker removes only enumerated proof imports,
annotations and an erased identity observation, then compares every remaining
byte with the checksum-pinned release. The two other methods remain unchanged in
native builds but are excluded from this Creusot configuration.

The contract requires only the selected closure's `FnOnce` precondition. If the
method returns, its result satisfies that closure's postcondition; the unused
closure is resolved in Creusot's model without an invocation precondition. The
trait refinement and the observation `option_model(self) = self` are checked.
This is partial correctness, not a termination theorem or a proof of arbitrary
callback effects/destructor panics. Standard `Option::map_or_else` and `FnOnce`
contracts are trusted library boundaries; a generated standard-contract stub goal
does not prove the Rust standard-library body. See `verification/specification.md`
and `proofs.toml` for scope, assumptions and exclusions.

## Tools and reproduction

Use Bash, Python3.11+, Rustup, Git, Cargo and the existing native macOS arm64
Opam Creusot switch. No Aeneas environment is activated. Tool sources, compiler,
models and generated prelude are pinned to unmodified Creusot0.13.0 commit
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`; extraction uses
`nightly-2026-06-22`. The Cargo dependency pins that same official Git revision.
Native tests use Rust1.94.1.

The existing Opam Why3/Why3find and installed Z3 are reused read-only, with exact
versions, source revisions, binary/runtime hashes and active model hashes in
`toolchain.lock.json`. This host has Why3 1.8.2+git, Why3find1.3.0+dev, Z3 5.3.2.
These differ from Creusot0.13's recommended prover bundle; fresh valid proof
sessions establish operation for the pinned combination. No tool source is
patched and no user configuration is replaced.

```sh
bash option-ext/0.2.0/creusot/scripts/setup.sh
bash option-ext/0.2.0/creusot/scripts/verify.sh
```

Setup builds only the isolated0.13 Rust compiler/launcher and prelude if missing.
It restores the immutable release, fetches locked dependencies and checks active
Git model bytes against the compiler source. It defaults to the existing
`$HOME/.creusot/_opam` switch and platform-installed prover directory; override
`CREUSOT_OPAM_PREFIX` and `CREUSOT_PROVER_DIR` to select identical pinned tools.
`CREUSOT_GIT_CACHE` can seed the official compiler checkout. A differing binary or
runtime hash requires explicit review, a lock update and fresh evidence; it is
never silently accepted. `--offline` setup uses prepared caches.

The verifier creates a new run directory, new Cargo output and new proof sessions,
executes the standard `cargo creusot --no-cache --why3session` command, and requires
all four positive roots to be valid: product body, trait refinement, identity
observation and separately classified standard-model abstraction stub. It also
runs the three native branch tests and three doctests separately and compares
before/after source/tool/model fingerprints. A sandbox may block Why3's local
server socket; run the same command with the required process permission.
Current evidence belongs in `verification/results.md`, not this scope guide.

## Separate report submission

The existing Aeneas report is preserved. `scripts/check-api-discovery.py` exercises
the actual pinned recorder scanner and requires exactly the qualified concrete
`map_or_else2` API with its selected-branch premise. Publication uses the already
prepared, read-only proofs-rs CLI from this version's parent tool cache; only that
CLI is reused, with no Aeneas proof activation.

After reviewed source is committed and pushed, `scripts/record.sh` invokes the
standard recorder command, supplying the validated0.13 installation through
`CREUSOT_OPTION_CACHE` so detached worktrees use the same compiler, prelude and
Cargo cache. Recording/import classification and service publication are separate
from the four-root functional evidence. Source publication and report upload
require explicit user authorization and are handled by the primary agent.

Recording should start from a stable external clean Git worktree when an ancestor
Cargo configuration injects unrelated patches. The normalized lock contains no
unused local patch markers. Setup metadata/fetch and native checks run from an
external directory with explicit manifests; proof runs use a fresh external
workspace and copy the checked source and complete proof artifacts into the run.
The recorder wrapper first checks that its working directory's Cargo configuration
can use the lock without changing it. For this host, the primary records and
publishes from `/private/tmp/option-ext-creusot-report-<commit>`, with
`CREUSOT_OPTION_CACHE` pointing at the prepared original `.work` installation and
`CREUSOT_PROOFS_RS_STORE` pointing at the already pinned recorder. Keep that
worktree path stable through publication because the CLI indexes state by the
absolute manifest path. The transient Git HTTPS rewrite is inherited separately.
