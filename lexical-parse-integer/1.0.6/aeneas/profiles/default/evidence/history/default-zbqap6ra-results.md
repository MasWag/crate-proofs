# Verification results

The final offline managed run `default-zbqap6ra` **passed locally** on
`aarch64-apple-darwin`. It restored and checked the checksum-pinned
`lexical-parse-integer` 1.0.6 release, compared fresh Aeneas output byte for
byte with the maintained model, ran native tests separately, cleaned and rebuilt
the local Lean package, and audited 28 named theorems. All four API/theorem
mappings matched this profile's `proofs.toml`; only `propext`,
`Classical.choice`, and `Quot.sound` occur in their transitive axiom sets.
Before/after input fingerprints matched. The exact local run and SHA-256
identities are in [evidence/summary.json](evidence/summary.json). Its full logs
remain under ignored `.work/runs/default-zbqap6ra`; there is no downloadable
archive or published report.

## Formal scope

Four total-success theorems prove the generated decimal-specialized bodies of
`algorithm::is_4digits`, `is_8digits`, `parse_4digits`, and `parse_8digits`.
For every packed 32-bit or 64-bit word, the recognizer returns `.ok out` with
`out = true` exactly when all four or eight bytes are ASCII decimal digits.
For every word satisfying that predicate, the decoder returns `.ok out` with
`out.val` equal to the independent positional decimal value in `Specs.lean`.
These are universal theorems, including leading zeros, rather than finite
sample checks. The audit includes 24 supporting theorems, including checked
arithmetic, a general byte-lane recognition argument, and total-success
bridges.

The checked Rust source is [verification/harness/src/lib.rs](../../../verification/harness/src/lib.rs),
derived from the four release SWAR helpers by removing the unused const
`FORMAT` parameter and replacing `NumberFormat::<FORMAT>::MANTISSA_RADIX`
with `10u32`. The checker `scripts/check-swar-adaptation.py` enforces exact
textual correspondence for every other function-body byte. This specializes
formats whose mantissa radix is 10, including the standard format. It is a
reviewed source correspondence argument, **not a formal Rust-to-Rust
equivalence proof**. The original helper extraction instead produced an
external `NumberFormat::MANTISSA_RADIX` axiom, which the extractor rejected.

The recognizer proofs connect the actual generated SWAR bit predicates to the
independent byte-level decimal predicate for every packed word. The proof uses
kernel-checked arithmetic across the byte lanes. An earlier `bv_decide`
attempt produced a forbidden native-decision axiom and was excluded from the
maintained proof and final audit.

The actual complete and partial parser bodies passed separate Charon probes,
but clean upstream Aeneas rejected their macro-expanded outer-loop breaks at
release `src/algorithm.rs:703–708` and `712–720`, respectively. The complete
parser's maintained
`scripts/check-original-parser-blocker.py` reproduced this boundary in the
final run and retained its logs under ignored `.work`. Two faithful source
trials, recorded as [no-multidigit](../../../verification/parser-no-multidigit.patch)
and [else-if](../../../verification/parser-else-if.patch) patches, still reached
the same Aeneas error after Charon success. The first trial removes the fast
loops for the `Options.no_multi_digit=true` domain; the second also makes the
post-negative-loop branch an `else if` for the default no-format path. Neither
trial is a verified parser, and neither modifies the locked release or Aeneas.
The separate ignored partial-parser probe and its log hashes are indexed in
[evidence/summary.json](evidence/summary.json); it is not a selected managed
extraction. Faithful loop/iterator refactoring
for both parsers remains separate work.

No theorem currently proves public parsing trait behavior, signs, overflow or
underflow error indices, consumed lengths, options equivalence, feature
equivalence, nondecimal radices, or custom format grammar. The
[coverage ledger](../../../SPECIFICATION.md#coverage-ledger-and-acceptance)
keeps these obligations open. The proved recognition and decoding slice does
not establish that the parser invokes the helpers correctly, advances its
iterator correctly, or composes decoded blocks with surrounding digits.

## Native tests and findings

The managed default-feature native stage passed 43 release/probe/doc tests:
8 algorithm, 12 API, 3 behavior probes, one issue-91, one options, one partial,
and 17 documentation tests. The derived harness compiled and its test stage
passed with zero tests. Native success is separate from the 28 formal theorem
audits.

Separate native `format,power-of-two` and `format,power-of-two,compact`
probes passed five controls each and reproduced four expected-correct assertion
failures in two behavior groups. The findings describe a single zero's short
partial consumed count and an unrelated invalid byte being counted in a suffix
format. Commands, exact outcomes, controls, and local log hashes are in the
[behavior record](../../../verification/behavior/README.md); the detailed
investigations are [LPI-001](../../../verification/findings/LPI-001.md) and
[LPI-002](../../../verification/findings/LPI-002.md). These are native
observations, not formal counterexample theorems.

## Inputs and limits

The source archive SHA-256 is
`9a7a039f8fb9c19c996cd7b2fcce303c1b2874fe1aca544edc85c4a5f8489b34`.
The latest-version registry resolution and date are recorded in
[release-resolution.json](../../../verification/release-resolution.json).
The profile pins unmodified Aeneas `be86ab0f1989d04944292b345b24c435be3ad10a`,
Charon `08d7c9d50144bd84848212c24701253585e90d1f`, extraction Rust
`nightly-2026-09-17`, native Rust `1.94.1`, and Lean `v4.35.0`.
The proofs-rs CLI patches in the tool lock do not change Aeneas or the Lean
model. Verification ran with a version-local `CARGO_HOME`, but root/harness
execution directories inherited the ancestor Cargo configuration. Its path
and hash are pinned and checked before and after by
[execution-config.json](../../../verification/execution-config.json); the
unused Creusot patch appears only as `[[patch.unused]]` in Cargo.lock. The
final run proves no other target or feature profile, and no recording, upload,
or publication was attempted.
