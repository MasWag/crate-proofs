# Preserved original-body verification

The final fresh integrated run
`.work/runs/run-20261103T134348Z-afzaahye` passed on 2026-11-03 for
`aarch64-apple-darwin`, with unmodified Creusot0.13.0 and its Git-pinned standard
models at commit `318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`.
This acceptance belongs to the original fingerprinted inputs; later input edits
require a new run.

The maintained `Option<T>` method retains the release body
`self.map_or_else(default, f)`. The strict correspondence check validates the
entire checksum-pinned release inventory, strips only the enumerated proof-only
additions and compares all remaining source bytes. The active Git standard-model
source bytes match the compiler source. The proof uses only the selected
callback's precondition and establishes its postcondition when the method
returns, including the modeled resolution of the unused closure. It does not
prove termination, arbitrary callback side effects or arbitrary destructor panics.
See the independent specification and report for the full scope and assumptions.

All four positive roots have fresh Z3 `valid` results in their Why3 XML sessions:

| Root | Meaning |
| --- | --- |
| `vc_map_or_else2_Option_T` | Original delegated product body |
| `refines` | Public trait-contract refinement for Option<T> |
| `vc_option_model_Option_T` | Checked identity of the erased receiver observation |
| `vc_map_or_else_T` | Standard-library contract abstraction stub; not the Rust std body |

The standard combined `cargo creusot --no-cache --why3session` command ran in a
fresh workspace containing byte-identical source, Cargo manifest/lock and Why3
configuration. Cargo build output and proof sessions were new. Copied inputs were
checked before and after proof. The runner rejects disabled Python assertions and
unpinned compiler/flags/output overrides. The selected read-only Opam tools were
Why3 1.8.2+git, Why3find1.3.0+dev and Z3 5.3.2; exact executable/runtime/prelude
hashes are recorded in `toolchain.lock.json` and the run fingerprints.

Native observations are separate: three branch tests and three doctests passed
using Rust1.94.1. They exercise all release methods in native builds but do not
extend this report's formal scope beyond `map_or_else2`.

Before/after input JSON SHA256, identical:
`62219022209345ac13e3e45dbae9a03d3edfff45b018326345c9115f03a8cf0c`.
The result JSON SHA256 is
`7919d14479d4a9f0cdd23040772d20ce169211c2ce9b572054b7e3c39b83ff27`.
`evidence/summary.json` and `evidence/archive.json` preserve the compact result
and complete local-only execution archive (Cargo build intermediates excluded).
The archive was re-read and every member compared with its original run file.
It has no public download URL.

Earlier probes remain local and are not promoted as final acceptance. In
particular, one standard prover attempt failed to create its Why3 server socket
inside the sandbox. An initial fresh-output runner then caught that Creusot0.13's
`--output-dir` compilation output did not select the new directory for proving;
its missing proof JSON caused a closed failure. The final runner uses a fresh
copied workspace and default proof path, matching ordinary recording semantics.
These are environment/runner issues, not defects in option-ext.

Actual pinned proofs-rs scanner discovery selected exactly
`<core::option::Option<T> as option_ext::OptionExt<T>>::map_or_else2` with the
selected-branch premise. Recording and service publication remain separate from
this local functional/refinement evidence; no importer classification is inferred
from older CLI versions. The existing Aeneas report is preserved.

The final acceptance also uses a normalized Cargo lock with no unused local0.15
patch marker. Cargo metadata/fetch/native checks use an external working
directory and proof uses a fresh external workspace, so an unrelated ancestor
user Cargo configuration cannot inject that marker. Actual source snapshots and
all proof sessions are copied back into the immutable run. A prior recording
attempt proved the body but was rejected for tracked Cargo.lock changes after
Cargo removed the ambient unused marker outside the user's home directory;
this was a recording-environment issue, not a source or verification defect.
The recorder-only wrapper syntax excludes the nested Cargo argument delimiter
rejected by the pinned CLI; the formal proof command and contracts are unchanged.
