# Coverage ledger

This file defines selection and exclusions. Execution outcomes, counts and saved
run identities belong to [results](results.md). Exact generated names and required
core bodies are enforced by [target-inventory.json](target-inventory.json).

| Surface | Selected contract or boundary |
| --- | --- |
| `unindent_bytes` | Arbitrary representable byte slices; exact complete ordered `source_unindented` result, output non-growth, successful termination |
| Private `do_unindent_bytes` | Same exact contract for both values of the first-line flag; includes all content branches, bounds and loop variants |
| `common_margin` | Attained exact minimum of later nonblank source-line indentation, zero if none, successful termination |
| `unindent`, private `do_unindent` | Exact output byte relation and non-growth; checked UTF-8 preservation discharges conversion and unwrap; successful termination |
| `[u8]`, `str`, `String` concrete `Unindent` implementations | Corresponding exact body contracts; every generated refinement selected |
| Scanning and copy helpers | Exact prefix/range contracts, bounds and termination; `append_range` is retained but unused by the final byte scan |
| Source-position helpers | First nonwhite witness, line-start facts, complete ordered trace extensions, and retention of every non-ASCII byte |
| UTF-8 and trace helpers | Checked sequence identities, ordered ASCII erasure, scalar encoding composition and output encoding validity; all generated helper roots selected |
| Std encoding/conversion models | Trusted standard boundaries in [assumptions](assumptions.md); not application proofs or selected positive targets |

No generated application target is intentionally excluded. The runner rejects a
missing, extra, open or empty selected proof session and checks the complete
Coma inventory. Runtime target annotations select termination; public APIs have
no input-content preconditions. Native tests run separately against immutable
release bodies.

The following remain outside the selected checked result:

- The generic `Unindent for &T` body is compiled natively but excluded under
  `cfg(creusot)`. Arbitrary user implementations need not terminate or return
  unindented contents. The prior Aeneas delegation theorem is separate.
- The independent nested line-decomposition relation `unindented` is defined,
  but its formal equivalence to `source_unindented` remains open. Independent
  mathematical review is recorded in the specification and contract review.
- The original iterator release bodies, `BytesExt::lines`, and all-input runtime
  equivalence between release and adaptation are not proved by this track.
- Allocation availability, capacity/pointer identity, external resource failures,
  other targets and MSRV compatibility are outside the models and run scope.

The source adaptation and finite agreement domains are recorded in
[source correspondence](source-correspondence.md). The exact byte contract is
substantive functional correctness for that adaptation; neither helper counts
nor service API claim counts establish release equivalence.
