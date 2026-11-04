# Further bs58 verification

This independent application workspace extends the accepted core proof without
modifying Creusot, its standard models, Why3, or the solvers. Its input contracts
are in [the independent specification](../verification/extensions/specification.md);
the [coverage inventory](../verification/extensions/coverage.md) separates the
selected operations from remaining model boundaries. Completion and acceptance
belong in the [results](../verification/extensions/results.md), not this guide.

The implementation is an adapted verification fork, with source correspondence
described [here](correspondence.md). It is not a proof of every unchanged release
body. The default-only codec adapters, full-feature checksum **state** projection,
mathematical round-trip relations, and actual runtime round-trip client are
separate coverage claims. Vector allocation/capacity failure and physical memory
behavior are outside the stock sequence model; generic callback termination and
whole-crate undefined-behavior freedom are not established.

From this directory, after preparing the parent workspace's
[pinned environment](../verification/toolchain-setup.md):

```sh
bash scripts/verify.sh
python3 scripts/check-native.py --toolchain 1.94.1
```

Native checking is offline and needs the locked registry packages cached. The
checker accepts explicit Cargo/Rustup homes when the existing native compiler and
cache use a separate installation. It fingerprints the compiler, application
sources, locked dependencies and every pinned release file before and after the
comparison. Native tests do not establish formal release equivalence.

The formal runner compiles into a unique output and Cargo target directory,
checks the exact generated-target inventory in `targets.json`, proves every file
without a proof cache, reconstructs original Why3 root goals, and validates every
proof tree. Computationally closed roots must pass a separate exact-root Why3
replay. Source, configuration, relevant tool executables and standard-model
fingerprints must remain unchanged. The extension-local checker recognizes
explicit trait-refinement declarations; the historical core checker remains
unchanged. Failed runs stay under ignored `../.work/extensions/`.

The [stock-model probes](../verification/extensions/model-boundaries.md) and
[optional-container probes](../verification/extensions/optional-boundaries.md)
identify precise missing contracts rather than treating old scope exclusions as
proof blockers. These diagnostic workspaces are not product API coverage and
deliberately include calls with impossible preconditions.

The publication recorder uses a separate fixture under `publication/` with a
registry-known package identity. Preparing a fixture or editing report prose is
not a proof or publication. Only a successful standard recorder run and confirmed
service response establish publication status.
