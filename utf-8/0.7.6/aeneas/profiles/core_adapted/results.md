# Adapted core results

The final managed run `.work/runs/core_adapted-wxypzpfo` passed extraction, Lean
build and the audit of three named theorems. Native tests were run separately.
Run artifacts under `.work` are ignored and local-only.

For an initial length at most four, `splice_prefix_total` establishes a
successful model return, exact copied length and full buffer contents, and
preservation of the stored length. `classified_total` establishes the resulting
buffer, endpoint, consumption and tag when the descriptor-selected endpoint is
between the initial length and the end of the copied prefix. The decomposition
lemma is also audited. These are private helper results and do not claim a
public API proof.

The source is adapted: the wrapper still invokes the real standard UTF-8
validator, while the selected helper receives a descriptor. Neither the
descriptor's relation to the validator or Unicode grammar nor formal
equivalence of adapted and release code is proved. The
[correspondence record](correspondence.md) describes the patch and source-review
argument. The unchanged release-body profile has its own
[results](../default/results.md).
