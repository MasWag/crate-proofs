# Creusot results for the unindent 0.2.4 adaptation

## Accepted local proof

Fresh run `creusot-KG6tgwwd` on 2026-11-05 passed native checks, fresh Coma
compilation, standard Why3find verification and the shared independent audit.
The [manifest](evidence/latest/manifest.json) records **36 selected targets and
61 closed root goals**, with zero expected-open and zero excluded generated
targets. These are proof-file/root counts, not public API claim counts.

Manifest SHA-256:
`3231fc7230d64581d3f83a3d27f4579e4e1aa1f1823213d47606440a24eab025`.
The [audit](evidence/latest/audit.json) reconstructed the exact root inventories
with Why3 and checked the complete generated Coma inventory. Every selected
session has positive goals and every saved proof tree closes. Standard proving
exited 0 with `Proved (36 files)`. The before/after fingerprints match exactly,
including source, specifications, selection, scripts, configuration, resolved
annotation sources, installed models/drivers, compiler binaries, solver binaries
and Why3 server. The audit checks saved consistency; the fresh runner and its
logs separately establish execution. It is not certificate checking.

Run from the Creusot workspace with `bash scripts/verify.sh`. The selected
portfolio is Z3 4.15.3, CVC5 1.3.1 and Alt-Ergo 2.6.2, through Why3find
1.3.0+dev and Why3 1.8.2+git. Compile and native target directories, generated
Coma and proof sessions were fresh. Caching was disabled for proving.

The exact environment is in [versions](evidence/latest/versions.txt) and the
manifest's resolved paths/hashes. Creusot 0.13 uses extraction compiler
`nightly-2026-06-22`; native checks use Rust 1.91.0 on Linux x86_64.
The installed verifier source checkout remains clean at
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`. No verifier source was changed.
Resolved `creusot-std` and its proc macros are registry 0.13.0. An inherited
0.15.0-dev Cargo patch is unused; its presence is not selection of that model.

## What is established

For the adapted implementation, the public byte API, its flagged private core,
string APIs and concrete `[u8]`/`str`/`String` extension bodies satisfy exact
`source_unindented` byte contracts, input-relative non-growth and selected
termination obligations. The margin is an attained minimum, and the output
trace is ordered and complete. Byte inputs have no content restrictions.

The string wrapper's conversion and unwrap obligations compose with checked
UTF-8 preservation. The application proof derives ordered ASCII-only erasure,
then preserves a character-encoding witness. The additional trust consists of
narrow std encoding and conversion models in [assumptions](assumptions.md),
including two character-encoding laws; no application algorithm or output-validity
claim is trusted. Every generated helper and concrete refinement is selected.
The str/String refinement roots check compatibility with the unconstrained
trait; exact output guarantees come from the concrete body contracts.

The [coverage ledger](coverage.md), [contract review](contract-review.md),
[independent specification](specification.md), and
[source correspondence](source-correspondence.md) define scope. Astra designed
and reviewed specifications; Sol implemented the adapted runtime and proofs;
Terra drafted report prose, which Astra independently reviewed. The primary
reviewed commands, source identities, inventories, scope and evidence. Astra
independently accepted the final raw evidence: all session trees and generated
targets match, all current source/tool hashes match, and the audit's manifest
digest is correct. Its raw VC review includes bounds, attained minimum, exact
contents, termination, conversion success and concrete refinement obligations.

## Separate native observations

The [native log](evidence/latest/native.log) records passing comparisons with
immutable release bodies:

- 300,617 byte inputs: all sequences of length 0–6 over NUL, TAB, LF, CR, SPACE,
  `A`, 128 and 255, plus deterministic arbitrary-byte cases of lengths 0–1023.
- 299,593 Unicode inputs: all strings of length 0–6 over NUL, TAB, LF, CR,
  SPACE, `A`, `é` and `🦀`, exercising free and concrete extension APIs.
- 74,898 input/flag pairs: all strings of length 0–5 over that Unicode alphabet,
  with both private flag values, comparing adapted string and byte cores.

These finite observations do not establish formal release equivalence. No new
confirmed crate defect was found during this continuation. The prior CRLF
behavior question remains in [Aeneas report #20](https://proofs.rs/report/20).

## Remaining proof boundaries

The original iterator pipeline cannot be extracted by this frozen Creusot model:
`slice::Split<u8, fn(&u8)->bool>` lacks `IteratorSpec` at `.lines().skip(1)`.
The subject therefore uses indexed margin discovery and a bytewise retention
scan. Its [runtime adaptation patch](patches/creusot-source.patch) is disclosed.
No all-input equivalence theorem between this executable and the release is
proved. The independent nested line-decomposition specification and checked
source-position specification have mathematical review, but their formal
bridge remains open. These are distinct from the zero open goals within the
selected adaptation proof.

The generic `&T` extension is native-only in this workspace and excluded from
Creusot selection; arbitrary downstream implementations have no universal
success/content guarantee. Prior Aeneas delegation evidence remains separate.
Allocation availability, physical capacity/pointer behavior, resource exhaustion,
other targets and MSRV compatibility are not established.

The first integrated trial `creusot-H0oNGa9g` left `trace_keep` open when restricted
to Z3/CVC5. The exact unchanged obligation closed in a fresh diagnostic run with
Alt-Ergo. The final fresh portfolio includes it; no source, contract or assumption
change was needed. Failed/trial artifacts remain in ignored `.work` and are not
promoted as accepted evidence.

## Recording and publication

Local functional and termination proofs are distinct from service claims. The
pinned cargo-proofs 0.4.1 Creusot importer records only `panic_contract`, not
additional `functional_correctness` or `no_ub` service claims. The reader-facing
[report configuration](../proofs.toml) makes the adaptation and trust boundaries
explicit. Standard detached-source recording and publication are pending; the
previous Aeneas report is unchanged by this local acceptance.
