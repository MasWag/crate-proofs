# option-ext 0.2.0

This independent Cargo workspace pins the latest stable `option-ext` release found
in the official crates.io sparse index on 2026-11-03. Its checksum and complete
release file inventory are in `source.lock.json`; unchanged release files are
restored into ignored `.work/source`.

| Public method | Formal scope |
| --- | --- |
| `OptionExt::contains` | Actual unchanged release body; returns false on None and invokes the heterogeneous comparison in candidate-to-payload order on Some. |
| `OptionExt::map_or2` | Actual unchanged release body and extracted actual standard-library `Option::map_or` body; returns the default on None and selected callback result on Some. |
| `OptionExt::map_or_else2` | Disclosed direct-match adaptation; returns the selected default or mapping callback result. The original delegated release body remains blocked in the pinned extractor. |

The mathematical specifications require success only of the selected comparison
or callback. Exact branch equations also establish propagation of its translated
failure result. They impose no symmetry/reflexivity on heterogeneous comparison
and no totality on an unused callback. The checked model does not establish
arbitrary external effects, runtime call traces, destructor behavior, resource
use, or Rust-to-Lean translation soundness. The reference `PartialEq` adapter and
closure dictionaries are Aeneas backend model boundaries. Specification design,
proof implementation and independent review were performed separately.

The adapted source is generated in `.work/adapted` by
`scripts/check-adaptation.py`. That checker permits precisely one replacement:
`self.map_or_else(default, f)` becomes
`match self { Some(value) => f(value), None => default() }`.
The public signature, trait, and all other release bytes are preserved. The
checker validates exact bytes and records original/adapted hashes before and
after verification. Source correspondence is reviewed, not a formal equivalence
theorem. Generated Lean is never edited. Aeneas and Charon have no patches.

The original third-body failure can be reproduced with the maintained
`extraction-original-all.json` through `scripts/check-original-blocker.py` after
setup and with the selected tools on PATH. The full verifier does this separately
and retains the expected `Found unexpected constant: ()` failure at the standard
`Option::map_or_else` nullary callback. Partial output is not accepted as proof.

## Reproduce

Requirements include Python 3.11+, Git, Rustup, Elan, Opam, a C/OCaml build
environment, GMP and pkgconf. The accepted target is `aarch64-apple-darwin`.
The locked tools are native Rust 1.94.1, extraction Rust nightly-2026-09-17,
Lean 4.35.0, Aeneas `be86ab0f1989d04944292b345b24c435be3ad10a` and its
compatible Charon `08d7c9d50144bd84848212c24701253585e90d1f`.

From the repository root:

```sh
bash option-ext/0.2.0/scripts/setup.sh
bash option-ext/0.2.0/scripts/verify.sh --offline
```

Setup restores and checks immutable source, builds the pinned toolchain, and
prepares locked Lean dependencies. The first build needs network access. On this
macOS host, setup bootstraps GNU Make 4.4.1 locally under `.work/gnu-make` using
`scripts/bootstrap-make.sh`; its official GNU archive SHA256 is checked before
building. Nothing is installed system-wide. When the installed Homebrew GMP
header and pkgconf executable are present, setup bypasses Opam's failing system
dependency detector. It uses rustup proxies instead of the independent Homebrew
Cargo binary.

A setup-only Cargo wrapper runs compiler-build Cargo commands from a temporary
external directory with explicit original manifests and the selected Rustup
channel. This prevents an unrelated ancestor user Cargo patch from modifying
Charon's locked source. It does not wrap proof extraction or native verification.
The local Cargo lockfiles contain a harmless unused `creusot-std` patch marker
needed by this host's ambient Cargo configuration; it is not a dependency or a
Creusot activation. Locked tests were also checked from an external directory
without that configuration. The actual dependency graph is empty.

The shared managed verifier checks source/tool identities, regenerates and
compares both maintained Lean models, runs native tests separately, cleans only
the local Lean package, builds and audits every named theorem, and checks stable
before/after fingerprints. Results and immutable run logs remain under ignored
`.work`; `aeneas/profiles/default/results.md` describes current acceptance.
Native evidence includes three release branch tests and three release doctests,
plus three tests of the adapted harness. Native tests are not formal proofs.

No crate defect was found in the reviewed three methods. The extraction boundary
is not reported as a crate bug. Local setup and verification do not push or publish evidence.

## Recording and submission

`proofs-prepare.toml` wires the pinned CLI to source restoration and managed
preparation before callable discovery, including in a detached Git worktree.
`scripts/check-api-discovery.py --offline` exercises the actual pinned CLI modules
and checks all three qualified concrete trait-implementation paths and their exact
preconditions. A version-owned proofs-rs scanner patch normalizes raw module
identifiers (`mod r#impl;` loads `impl.rs`) and Rust2015 direct crate-root
imports (`use OptionExt;`). All24 scanner regressions pass, including external/inline
raw modules and preserving rejection for the same alias in Rust2018. This changes recording discovery, not Aeneas, Charon or the Lean model.

After committing and pushing the reviewed verification inputs, run:

```sh
bash option-ext/0.2.0/scripts/record.sh
```

The wrapper supplies validated shared tool/archive/Lake caches, runs the pinned
CLI's standard Lake build and audit from the prepared Lean directory, and records
results without uploading them. `cargo proofs publish` is a separate submission
action requiring explicit authorization. Source publication and service publication remain separate from local formal
acceptance.
