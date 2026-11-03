# bs58 0.5.1 Creusot verification plan

## Identity and constraints

The target is registry bs58 0.5.1, archive SHA-256
`bf88ba1141d185c399bee5288d850d63b8369520c1eafc32a0430b5b6c287bf4`.
The parent `source.lock.json` inventories the unchanged release; all 24 recorded
file hashes were checked before restoring this workspace's independent reference.
See [release identity](release-identity.json).

The user requires an unmodified Creusot toolchain, Astra specification design,
Sol proof implementation, and retained findings. Application adaptations are
permitted with explicit correspondence. The historical Aeneas profile is preserved.
The selected compiler is official Creusot 0.13.0 commit
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`, with nightly-2026-06-22.
The existing user opam switch supplies Why3 and why3find read-only; configuration
and proof outputs are isolated in the writable workspace.

## Core scope

The standalone `no_std` proof crate selects the unchecked byte-conversion core.
Native reference tests additionally enable upstream `check` and `cb58` for bug
reproduction. These feature sets have different evidence scopes.

| Function | Intended guarantee | Correspondence boundary |
| --- | --- | --- |
| `Alphabet::new` | Exact ASCII/duplicate errors, exact forward and inverse tables | Same constructor algorithm; fork-local error type and proof interface |
| `encode_into` | Complete Base58 output including leading zeros, exact capacity result, untouched success suffix | Specializes the private generic encoder to byte slices; index loops and explicit reversal |
| `decode_into` | Complete decoded output, exact character/capacity error order, untouched success suffix | Index loops, explicit capacity tests and reversal |
| `decode_into_const` | Same decoding/error relation, with zero padding after the decoded prefix | Fixed-array implementation with fork-local error type |

The independent [specification](specification.md) includes arbitrary input bytes,
empty inputs, insufficient buffers, every valid ASCII alphabet, and termination.
Codec preconditions require a valid alphabet; construction must establish that
invariant, rather than assuming arbitrary tables are valid. Source contracts are
not proof results. Recursive mathematical helpers and their termination obligations
belong to the accepted proof inventory along with all selected function bodies.

## Trust and exclusions

There must be no application `trusted` computations, additional axioms, or unchecked
replacement of a conversion algorithm. Shipped Creusot models, the Rust compiler,
Why3 and the SMT solvers remain part of the trusted verification infrastructure.
No tool or standard-library model patch is allowed in this trial.

See [correspondence](../correspondence.md) for runtime changes and excluded derived
traits. Finite native comparisons do not prove release/fork equivalence for all
inputs. The public builders, arbitrary generic iterators/targets, allocation,
UTF-8 string targets, checksum implementations and cryptographic properties are
outside the selected body proof. Existing checksum defects are separate
[findings](findings/README.md); no source fix is applied.

## Acceptance

Translation, native tests, differential observations and formal proof are recorded
separately. Formal acceptance requires a fresh, cache-disabled proof run with a
complete generated-target inventory, positive verification conditions, every
selected goal tree closed, normal process exit, and equal before/after fingerprints
of source, specifications, configuration and relevant tools. Intermediate runs and
open goals remain diagnostic evidence. Updating prose does not refresh a proof.

The feasibility milestone has reached translation of all four core bodies and
actual solver execution. Continue with the requested core contracts; keep
unresolved requirements visible rather than substituting wrapper-only claims.
