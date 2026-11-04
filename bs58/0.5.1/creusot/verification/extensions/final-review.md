# Independent final extension review

Accepted for the selected verification-fork scope. This independent Astra review
inspected the source and intended contracts, generated calls and refinements,
complete fresh evidence, native correspondence evidence, and Terra's editorial
draft. It does not promote the unchanged release or excluded APIs into coverage.

## Accepted evidence

The canonical fresh run is `.work/extensions/formal-vkijxx6d`. Translation,
proving and audit all exited zero. The exact frozen inventory contains 135
emitted targets: 126 body/helper/initializer targets and nine trait refinements.
All 242 reconstructed roots match the proof-session root sets, each selected
target has a positive root count and its expected target goal, and all trees
close. The evidence separates 612 solver leaves from 123 computed root closures.
All computed closures have successful exact original-goal selection, one
unambiguous expected printed original goal, and successful transformation with
zero residual output. These counts are proof obligations, not public API counts.

I independently checked the complete inventory, every recorded Coma/proof JSON
hash, root-set equality, target goal presence, computed-replay identity maps,
zero exits and residuals, before/after fingerprint equality, and current hashes
of every fingerprinted file. The input fingerprint is
`ab390693bf082b1e018f9a852b34ce134dbbb9656f0825f95ed5d1cc339daca2`;
the goal-inventory hash is
`c30b1f8669e801c356eaff0f81d42ee91f3ceeaa488de574b3d12227d70af065`.
The native run `.work/extensions/native-7eq5hgpv` has unchanged before/after
inputs and the same nine application-source hashes as this formal run.

The local checker preserves the original root reconstruction and guarded
computational replay. Its narrow additions recognize explicit `goal refines`
files and the stock Why3 printer's apostrophe-to-`qt` spelling. I inspected the
diff and installed Why3 namespace lookup and identifier/printer sources, and
independently ran eight synthetic gate controls and six real Why3 controls.
Missing/empty proofs, wrong roots/declarations/filenames, nested empty trees,
missing requested goals, colliding aliases and false residual goals reject.
The accepted checker hash is
`fb2331417430772366acab207c31b30a0a12ea2614b1e24d6b9ee315c84c7eaf`.
This changes local evidence recognition, not the verifier, models or goals.
The earlier `formal-f04h1fbu` audit rejection and interrupted `formal-xaabyf9a`
are retained attempts, not accepted runs; replaying their artifacts did not
replace the final fresh run.

## Contract and composition assessment

The concrete slice and decoder-array wrappers preserve complete core results,
capacity-dependent errors and successful suffix preservation. Their generated
calls use actual callback/reference dispatch, including the final-borrow
relations. Concrete single-call bodies support the invocation claim; the
logical callback relation alone is not an independent event trace. All selected
target refinements close. Arbitrary upstream targets or unstable AsRef inputs
are not covered by these specialized laws.

The vector adapters call the checked core directly and use checked push-zero
and pop helpers. Encoder capacity is proved without an assumed fit predicate;
decoder capacity handles valid input, and an additional valid-prefix argument
excludes numeric capacity errors even for malformed input at full-input-length
capacity. Error contracts retain the original prefix and enlarged logical
length, leaving error-tail bytes unconstrained. Exact tail-state or rollback
claims would be stronger than the proof. Allocation success is modeled:
physical capacity-limit panics and resource failures remain outside the model.
Capacity, pointer identity and allocation-call sequence are not observations
preserved by these adaptations.

Both mathematical inverse relations use positional uniqueness and exact leading
zero counts. The encode-then-decode runtime client actually calls both codecs
and discharges capacity/error premises. The reverse relation has no separate
runtime client. Unwrap methods have explicit successful-input premises; they
are not unconditional no-panic results. Extension wrappers and vector loops
carry no blanket total-termination guarantee.

Actual numeric-byte constant initializers call the checked alphabet constructor;
default frontends bridge the actual DEFAULT table through crate-private
from_input. MONERO uses Bitcoin's bytes with equal tables, not pointer identity.
The separately proved nine-body checksum-state projection preserves fields and
sets exact modes/versions; it neither proves SHA nor composes with enabled
codec execution. Manual exact-copy error Clone bodies preserve char fields
without assuming an absent char-clone law. Selected error equality refinements
and Alphabet Clone are covered; formatting and all derived traits are not.
No trusted application algorithm, unchecked application assumption or added
external specification was found in selected source.

## Native and editorial review

The native run compares 82,944 slice cases, 80,819 array cases and 43,200 vector
cases against the pinned registry release, plus built-in/default cases and
3,600 actual composed round-trip assertions. I inspected its log, harness and
source-fingerprint intersection. Complete-buffer comparisons concern byte
contents and logical lengths on success/error, not capacity, pointers or
allocation traces. These finite observations support reviewed correspondence,
not universal equivalence. The separate custom-target, repeated-AsRef and
String-error witnesses are semantic boundaries, not new defects.

Terra's final editorial JSON accurately distinguishes the fresh integrated
result from historical core evidence; mathematical relations from runtime
composition; state-only checksum coverage from digest computation; and
modified application bodies from the release. Requested revisions clarify
non-ASCII versus invalid-ASCII errors, the decoder-only array target,
allocation-model premises and vector observation limits. Exact error-tail,
whole-crate termination, undefined-behavior freedom, generic iterator/target
and cryptographic claims are not made. The additional optional-container
paragraph is supported by ten concrete no-contract compile diagnostics and
remains explicitly excluded from product proof coverage.

This review followed the repository Creusot verification/composition skills and
both repository and upstream-local report-writing skills. Final publication
mapping and artifact upload remain the primary agent's responsibility; this
acceptance concerns the inspected contracts, proof evidence and editorial scope.
