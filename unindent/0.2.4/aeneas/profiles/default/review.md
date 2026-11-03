# Independent correctness review

Reviewer: specification agent, separate from proof implementation. Review date:
2026-11-03. This record distinguishes inspected raw artifacts from obligations
that still require checked evidence. It grants no public API verification status.

## Release semantics

Inspected `.work/unindent-0.2.4/src/unindent.rs` directly. The specification's
LF decomposition, initial-CR special case, exclusion of the first line from the
minimum, byte-counted SPACE/TAB prefixes, blank-line handling and generic trait
delegation agree with the release implementation. Interior CR is content for
margin calculation. The CRLF discrepancy remains a candidate intended-behavior
issue; exact implemented behavior and desired line-ending invariance are distinct
contracts.

## Original core extraction

Inspected `.work/probe-two/aeneas.log`. The log reports unsupported locally
quantified regions in function-pointer arrow types and lifetime constraints in
the `BytesExt::lines` and `count_spaces` callback boundaries. It also warns that
the Lean iterator model lacks `filter_map`, `skip` and `min` fields, and reports
generation of a **partial** Lean file after 19 errors (6 unique errors).

This is an extraction blocker for this attempted core selection. It is not a
Rust counterexample or evidence that unindent's core is inherently unverifiable.
The partial file must not be promoted to an accepted generated model, even if
some helper declarations in it appear usable. A fresh successful selection or
a separately disclosed faithful Rust adaptation is required.

## Unchanged helper extraction

Inspected `.work/helper-one/Unindent.lean` and `extraction.json`. The extraction
record explicitly states `extracted-not-proved`. Its generated module contains
the actual `count_spaces`, `count_spaces_loop` and `count_spaces_loop.body`.
The body obtains `(index, byte)` from `Enumerate.next`, returns that index at the
first byte other than 32 or 9, continues on either whitespace byte, and returns
`none` on exhaustion. No application axiom or `sorry` declaration occurs in
this generated file. This inspection does not establish the axioms of imported
dependencies or prove total success.

Required helper contract: for every representable byte slice, successful result
is `none` exactly when all bytes are SPACE/TAB; otherwise it is `some k` where
`k` is the first non-SPACE/TAB index. A natural-number first-index specification
must be related to the returned `Usize` value, with its representability shown.

The generated loop invokes `Enumerate.next` before comparing the byte. Its
success argument therefore must cover the iterator's counter increment even
when the current byte immediately causes return. A general loop theorem needs
a bound such as counter plus remaining length at most `Usize.max`, or a stronger
bound from the concrete slice representation; it cannot claim success for all
arbitrary raw enumeration states. The public helper starts with counter zero,
so this loop invariant must be derived from actual slice bounds rather than
introduced as a content restriction.

The private helper is only one dependency of the requested algorithm. Neither
its extraction nor its eventual proof establishes line splitting, margin
selection, byte output, UTF-8 closure or any public extension API contract.

## Pending review gates

- Inspect any Rust adaptation against the unchanged release and mathematical
  specification, including terminal empty fields, initial CRLF and blank lines.
- Inspect actual theorem statements and full dependency/axiom audit, with
  successful Lean build logs and regenerated-model comparison.
- Inspect native reproduction results separately from formal proof evidence.
- Check report/API inventory mappings against the public coverage ledger. No
  public algorithm claim may be inferred from a helper-only theorem.
- Check release source identity, tool pins and relevant before/after input
  fingerprints in the primary's final evidence bundle.

No completed formal proof, adaptation equivalence proof or report acceptance
has been reviewed at this stage.

## Follow-up independent review of implemented contracts

A separate correctness-review agent inspected the maintained generated modules,
`Proofs/Delegation.lean`, `Proofs/CountSpaces.lean`, source lock and restored source,
extraction selections, theorem inventory and report draft on 2026-11-03. This is
independent of proof implementation. The earlier specification agent could not
resume because of a thread-store error; this follow-up does not represent a
continued review by that agent.

All nine restored release files matched their SHA-256 entries in
`source.lock.json`, with no additional files in `.work/source`. The official
managed tool receipt under repository-root `.work/tools/42ae38a67d26f6feca8751544c66337c5089fc48f756ceab4a5572311fdb00ea/receipt.json`
records empty patch lists for Aeneas, Charon and proofs-rs and pins binary hashes.
Receipt inspection alone is not a fresh verification run.

The generic reference result-equality theorem is definitional equality to the
underlying trait call. Its public contract explicitly assumes successful
underlying execution and the chosen postcondition, then preserves both. It has
no premise establishing arbitrary implementations' indentation behavior. The
opaque-crate extraction includes the trait and generic reference implementation;
the concrete string and byte implementations are explicitly excluded. Thus this
is correctly conditional public delegation coverage, not core algorithm coverage.

The private helper's `CountSpacesPost` means that `none` requires every byte to
be SPACE or TAB, whereas `some n` requires an in-bounds nonblank byte at `n` and
blank bytes at every smaller index. These cases determine precisely the intended
first-index result, including empty input. The total theorem quantifies over all
modeled slices without a content precondition. Its loop invariant ties the
iterator's counter and position to the original slice and proves earlier bytes
blank. Counter increment safety follows from the actual slice length bound.
The decreasing remaining-length measure supplies termination. These mathematical
contracts are appropriate; checked build and transitive axiom evidence are still
required before acceptance.

The exploratory explicit-index Rust patch appears to preserve the specified
semantics on inspection, including initial CRLF and terminal empty fields.
This inspection supplies no formal equivalence theorem and the adapted core
must remain outside reported proved coverage.

At this review point, final integration is pending: managed regeneration must
include the helper module, the inventory must include its contract, stale
migration blockers must be updated, and core failed/partial extraction must not
be described as successful extraction. Native CRLF reproduction evidence and
final audit/fingerprint evidence have been requested from the primary.

## Accepted managed proof evidence

The follow-up reviewer inspected raw evidence in
`.work/runs/default-f7m_pbn3`: managed and audit `result.json`, both named-audit
logs, the Lean build log, native test log, and regenerated modules. The managed
run passed, both maintained generated modules match their fresh extractions,
and before/after input fingerprint hashes agree for both the managed run and
its theorem audit. The run artifact hashes were independently recomputed.

All three inventoried theorems passed the named theorem and transitive axiom
audit: the two delegation theorems and private
`UnindentProof.countSpaces_total_exact`. The helper's printed dependencies are
exactly `propext`, `Classical.choice`, and `Quot.sound`. Its final total-success
proof eliminates divergent and error results using the established weakest
precondition. No application axiom or admitted theorem is accepted. The updated
inventory classifies the helper as support, retains only one public API mapping,
and explicitly distinguishes blocked original core extraction from unproved
adapted core extraction. The managed verifier now regenerates both modules.

This evidence accepts conditional shared-reference delegation and total exact
private leading-whitespace classification for the unchanged selected release
bodies on the configured target. It does not accept either public core algorithm,
the concrete extension implementations, UTF-8 closure, or formal correspondence
of the explicit-index experiment.

Native checks are separate: the release crate has zero unit tests and two passing
doctests in this run. The separately compiled fixture
`verification/reproductions/crlf.rs` and `.work/crlf-native.log` reproduce the LF
and CRLF outputs shown in the report. The finding correctly asks about intended
behavior rather than asserting a proven specification violation.

The report must remove its stale pending-audit wording before delivery. Actual
CLI API discovery, formal recording, and publication remain distinct review gates;
this managed theorem audit checks mapping metadata but does not establish those
outcomes. The primary retains responsibility for final commands, final report
revision, and delivered coverage claims.

The final report writer's subsequent prose revision was independently rechecked:
it now states the private helper's total first-index result separately, removes
stale audit-pending wording, and preserves the conditional public guarantee and
all core exclusions. The revised claims agree with the inspected evidence above.

## Separate experimental scanner profile

The follow-up reviewer also inspected adapted `CoreAdapted.lean`, `Scanners.lean`,
the explicit source patch and preparation script, and native comparison source.
The independent scanner specification is in `../adapted/specification.md`.
The first-LF and bounded first-non-SPACE/TAB contracts are appropriate total
support contracts with explicit valid-range premises, not public API proofs.

Raw `.work/runs/adapted-b6mcfxzt` managed and audit results, build and named-audit
logs establish successful regeneration and audit of both scanner theorems.
Before/after fingerprints agree; artifact hashes were independently recomputed,
and fresh generated bytes match maintained `CoreAdapted.lean`. The native
comparison log reports 960,800 matching inputs over its stated finite alphabet
and maximum length. This accepts only these new adapted helpers; the full
adapted algorithm and its formal correspondence to the release remain unproved.

The primary is preparing final runs after CLI mapping/configuration updates.
Subsequent evidence review will be reported without modifying this fingerprinted
review record. Historical run acceptance here remains tied to the named runs.
