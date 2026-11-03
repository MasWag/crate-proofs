# Independent publication prose review

Reviewed on 2026-11-04 against the local official report-writing skill,
repository report-writing skill, specification, runtime correspondence, original
formal/native summaries, publication diagnostic summary, and the publication
fixture's four annotated entry points and mathematical result predicates.
This is a separate reviewer assessment, not a new proof run or archive audit.

The functional narrative is consistent with the inspected contracts: exact
alphabet errors, numeric value and leading zeros, necessary and sufficient
capacity, invalid-character/capacity precedence, successful suffix preservation,
and fixed-array right padding. Termination annotations cover all four entry
points. The original accepted summary reports complete discharged obligations.
The valid-alphabet premise, adapted-source boundary, absence of formal release
equivalence, finite-test distinction, and checksum exclusions are appropriately
explicit. The three finding descriptions agree with the recorded native summary;
this review did not rerun their snippets or independently check upstream status.
Reuse the existing report #13 finding texts without representing them as new.

Two corrections are required before approving the final publication prose:

1. Explain that the original proof/native fork uses the shared macro, whereas the
   publication fixture expands its Creusot branch into an ordinary public function
   with the same body and annotations. The publication fixture does not provide
   native `const fn` semantics for `decode_into_const`. Attribute the recorded
   constant-evaluation tests to the original native fork and release comparison.
2. Distinguish the original complete run (including computationally closed roots
   and their replay) from the fresh standard recorder run using direct solver
   search without compute preprocessing. The diagnostic summary explicitly says
   recording is pending; it cannot establish publication success. Once the fresh
   recorder succeeds, identify its evidence separately. State that the CLI's
   imported claim kind is panic-contract verification, while the broader
   functional narrative is supported by the separately identified complete proof
   evidence. Do not describe the old run's compute-root replay as part of the new
   recorder run.

The fixture README's creation-time byte-identical statement also needs a current
qualification pointing to `source-transformation.json`. Final evidence links
must resolve to the published immutable source revision. Historical evidence
summaries should remain historical rather than being overwritten to describe the
new fixture or run.

Verdict: functional scope approved; publication source/run attribution requires
the two corrections above and review of the resulting prose. No assertion here
that the fresh standard recorder or publication has already succeeded.

## Revised prose recheck

The revised editorial JSON now distinguishes the original macro from its direct
publication expansion, links the transformation, separates the original functional
proof from the fresh recorder, and explains the panic-contract import scope.
These resolve the substantive prose corrections. The native comparison sentence
should explicitly identify the original proof crate. Subject to that wording and
the primary verifying successful standard recording with all four intended API
entries and linked fresh evidence before publication, the revised prose is
approved. This conditional editorial approval does not substitute for that run.

## Final publication check

Inspected the final service payload and `recorded-run-summary.json`. The payload
now explicitly attributes native tests to the original proof crate and links the
fresh recording receipt at immutable revision
`b99e545a0ae7886785ee8f64b0897eb10d014d45`. The receipt reports successful standard
recording `8bd106e7-13c5-41b0-b8fa-901f2bb09834`, exit 0, four intended contracts,
and all 20 recorded roots passing, for source revision
`4e1eeb7de7f6c470dd3ec6e8dcf6066152de7784`. The final payload uses that run and
source, with the three codec alphabet preconditions and unrestricted constructor.
The historical functional evidence remains separately attributed.

The pending editorial conditions are satisfied: final publication prose approved.
This last check verifies attribution and receipt consistency; it is not a new
independent proof audit, service validation, or assertion of publication success.
