# Independent final correctness and evidence review

The separate final reviewer accepts the selected proof-fork contracts on the
evidence from `.work/creusot-run-8KtCLWaA`. This review inspected the independent
specification, all four Rust source files, the corresponding release bodies,
the runner and checker, generated Coma, raw proof JSON, and native evidence.
The reviewer did not implement or change the application contracts or proofs.

The final run has compile exit 0, aggregate proof exit 0, and exactly 56
per-target exit records, all zero. Its generated-target list equals the complete
Coma output inventory. Independently reconstructed Why3 roots agree with every
proof JSON root: 72 original obligations, with 542 successful solver leaves
(513 Z3 and 29 CVC5) and 16 separately replayed computational closures. Each
of the four selected bodies has its own positive proof tree:

| Selected body | Original roots in its file | Solver leaves | Computed roots |
| --- | ---: | ---: | ---: |
| `Alphabet::new` | 2 | 37 | 1 |
| `encode_into` | 5 | 123 | 4 |
| `decode_into` | 7 | 145 | 6 |
| `decode_into_const` | 6 | 145 | 5 |

The other generated files contain the checked mathematical definitions and
helper obligations. They are included in the same fresh run; helper completion
does not substitute for any selected body.

The 16 computationally closed roots are imported-call or standard-library
wrapper obligations, not omitted codec bodies. The reviewer independently
replayed each using standard Why3 with `-D why3`, selecting its exact theory and
goal. Every original selection produced exactly one goal; applying
`compute_specified` returned exit 0 with no remaining task. A nontrivial decoder
body remained a goal under the same transformation, and an invented goal name
failed with exit 1. Empty or missing trees are not accepted without this replay.
The frozen checker records these closures separately from solver leaves.

The inventory SHA-256 is
`24533045c88ff4bd44a5ffebe466a6acd5cc648ffdd163c51de303231c51a022`.
The computational replay record SHA-256 is
`dedb839ba3c16bca0615561e907422262a87649b1365c647aac2da17e2965a8a`.
Both match the actual final files. Before/after input fingerprints are identical,
and the reviewer independently checked their file entries against current files,
including scripts, Cargo configuration, compiler driver, prover binaries, and
installed Creusot models.

Creusot remains clean at
`318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`. Installed executable identities match
the toolchain record. The four installed generated model files are byte-identical
to those regenerated from that unmodified source. The native and proof logs
explicitly report the inherited Creusot 0.15 patch as unused; the selected
dependency is the pinned Creusot 0.13 source path.

The contracts retain complete positional-value and leading-zero semantics,
necessary and sufficient capacity conditions, exact error variants and positions,
capacity-dependent decoder error order, unchanged successful output suffixes,
and fixed-array right padding. `Alphabet::new` has no validity precondition;
the codecs require valid alphabet tables. No trusted application algorithm,
assumed arithmetic lemma, weakened postcondition, or missing helper dependency
was found. The proof uses the recorded x86_64 model and does not establish
whole-crate coverage.

The runtime correspondence remains a reviewed source argument supported by
finite tests, not a formal theorem equating the fork with the release. The
slice encoder excludes arbitrary `Clone + IntoIterator` implementations and
checksum chains. The shared const-decoder macro proves its fixed-array runtime
computation under `cfg(creusot)`; Rust compile-time evaluation semantics and
omitted derived traits are not formal claims. Builders, checksums, allocation,
formatting, string adapters, and round-trip composition remain outside this proof.

The strict native run `.work/native-final-ha3o_dyw` independently passed review:
exit 0, identical before/after snapshots, matching log and snapshot digests, and
all 24 registry source files present in both snapshots and matching the release
lock. Its harness covers 145,388 paired codec cases, 120,000 fixed-array
comparisons, 348 constructor outcomes, and the recorded const examples. F1–F3
were reproduced in both checksum modes. These are previously identified release
findings and native observations, not new checksum theorems or new discoveries.

The preliminary review identified a visibility typo in the correspondence
document. It was corrected before the accepted run's input fingerprint:
`Alphabet::new` is public in the release, while the three codec cores are private.
The corrected document matches the accepted fingerprint; no visibility erratum
remains.

Earlier interrupted combined runs and the run rejected by the original checker
remain historical evidence. They are not substituted for the accepted final run.
No source fix, upstream contact, publication, or push is part of this review.

The final results prose and compact evidence summary were also checked against
the accepted records. Their proof scope, counts, native distinctions, trust
boundaries, and source-equivalence limitations agree with this review. The compact
goal inventory and replay records are byte-identical to the accepted raw files.
