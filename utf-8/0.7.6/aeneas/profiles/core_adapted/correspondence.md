# Adapted core correspondence

This experimental profile is separate from default release-body coverage. Prepare
its input with `scripts/prepare-core-adapted.py NEW_DIRECTORY` after restoring the
locked release. The script applies source.patch and records SHA256 identities.
The source lock, immutable `.work/source`, and verifier tools are unchanged.

The patch replaces only `Incomplete::try_complete_offsets` and introduces
`Incomplete::classified_offsets` and `Incomplete::splice_prefix`. For initial buffer length n≤4, let
k=min(4−n,input.len()). Four guarded scalar writes copy precisely input[0..k] into
buffer[n..n+k]. They preserve every byte outside that range, including trailing
bytes beyond the reported event endpoint. This is the release slice copy's byte
behavior. For n>4 the changed location/kind of failure is outside correspondence.

The original-signature wrapper forms a copied local four-byte array with the same
splice, calls the real standard UTF-8 validator on its prefix n+k, converts the
observed success/error into `Result<(),(valid_up_to,error_len)>`, and delegates to
the classified helper. The helper calls the extracted `splice_prefix` to perform the same writes and retains the exact
release branch ordering: positive valid_up_to wins over error_len, checked
subtraction remains in each event branch, and pending copies all available input.
The additional local copy is unobservable in safe Rust. This is a source review
argument, not a formal release-to-adapted equivalence theorem.

The extraction selects only the helper, including all its buffer-writing and
classification-dependent control flow. The descriptor is an explicit parameter;
its equality to actual validator observations and its independent Unicode grammar
meaning are separate outstanding obligations. No placeholder descriptor is passed
by maintained adapted callers. The generated helper is not a proved decoder API.

The precursor scalar-loop adaptation retaining standard validation reaches the
same pinned standard validator translation boundary. Its diagnostic artifacts
remain `.work/core-refactor/scalar`; the successful classified/unrolled extraction
is `.work/core-refactor/splice`. The latter's generated file builds as Utf8Core in
`.work/core-refactor/proof`.

Reproduction command: `/opt/homebrew/bin/python3 scripts/probe-core-adapted.py`
from the version directory. The script generates a fresh lockfile for the derived
independent workspace under the pinned extraction environment, records extraction
exit status and leaves all output under `.work/core-adapted/run-*`. The first fresh
run was `run-eth700s8`, exit 0; its generated model is byte-identical to the model
used by the scratch Lean package. `splice_prefix` is extracted as an actual callee,
not substituted by a model. Adapted native release tests also pass separately
(`.work/core-refactor/native.log`); this is not formal proof evidence.

Independent source review also checked the wrapper’s eager `error_len()` read on
positive-prefix errors. The pinned standard implementation is a pure infallible
match on Option<u8> with a widening cast, so this extra read has no observable
effect. It supplies no independent proof of descriptor correctness.
