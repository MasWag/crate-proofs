# Independent Creusot specification: unindent 0.2.4

The specification agent owns this contract and independent review; the
implementation agent owns Rust adaptations, Pearlite definitions and proofs.
The primary reviews commands, tool/source identities, coverage and final claims.
This document specifies obligations, not completed verification. The separately
authorized Creusot track preserves the existing Aeneas sources, pins and proof
artifacts. Historical Aeneas acceptance remains tied to its archived inputs;
adding this workspace does not refresh that acceptance.

Source basis: the immutable release file `.work/source/src/unindent.rs`, pinned
by the version's `source.lock.json`. The independent byte semantics agree with
`aeneas/profiles/default/specification.md`; this track must not silently replace
those semantics. The adapted explicit-index implementation is a possible proof
subject, not automatically a theorem about the original iterator implementation.

## Mathematical byte model

Use finite `Seq<u8>` values, with mathematical integer lengths and indices;
`x[a..b]` means the subsequence on the half-open interval `a <= i < b`.
Sequence equality means length equality and pointwise byte equality, not merely
equal lengths or a relation between opaque output tokens. If a deep model uses
`Seq<Int>`, its connection to the byte view must be checked explicitly.

Let `white(b)` mean `b = 32 || b = 9`. Tabs count as one byte. Define `blank(l)`
by `forall j, 0 <= j < |l| ==> white(l[j])`. For a nonblank sequence, `indent(l)`
is the unique `k` satisfying `0 <= k < |l|`, all earlier bytes are white, and
`!white(l[k])`. It is not defined by a Rust traversal or display columns.

`prepare(x)` is `x[1..|x|]` exactly when `|x| >= 2`, `x[0] = 13`, and
`x[1] = 10`; otherwise it is `x`. Only the initial CR is removed.
`segments(x)` is the unique nonempty sequence of LF-free sequences
`[l0,...,ln]` whose LF-intercalation equals `x`, retaining empty leading,
interior and terminal fields. Thus `segments([]) = [[]]` and
`segments([10]) = [[],[]]`. Use this decomposition relation or a proved
equivalent mathematical definition, not an unchecked split model for the
application algorithm.

Write `[l0,...,ln] = segments(prepare(x))`. Define the finite eligible set
`E = { indent(li) | 1 <= i <= n && !blank(li) }` and the margin
`m(x) = min(E)` when `E` is nonempty, otherwise `0`.
The first line never contributes to the minimum. Set `t0 = l0` and
`ti = li[min(m(x), |li|)..|li|]` for `i > 0`.

For the private flag `p`, let `ignore(x,p)` mean `!p` and either `x` begins
with LF or `x` begins with CRLF. Define `U_p(x)` as LF-intercalation of
`[t1,...,tn]` if `ignore(x,p)`, and of `[t0,...,tn]` otherwise. The former
case necessarily has `n >= 1` and `l0 = []`. Public semantics are
`U(x) = U_false(x)`. Even when `p = true`, `prepare` still removes an initial CR.

Required characterization of the minimum: `m = 0` if no eligible line exists;
otherwise there is an eligible line with indentation `m`, and every eligible
line has indentation at least `m`. A lower-bound-only contract is insufficient:
the constant zero implementation satisfies that weaker contract.

## Public success obligations

For all representable byte slices, `unindent_bytes(s)` terminates without a
modeled panic and returns a vector with byte view exactly `U(s@)`. There are no
content preconditions, positive-margin conditions or UTF-8 restrictions on this
API. The stronger private `do_unindent_bytes(s,p)` contract returns `U_p(s@)`.
Both guarantee output length at most the input length. Arithmetic and indexing
must be safe for the actual Rust target's representable lengths, including empty
inputs. Allocation/resource behavior outside the standard-library model is
recorded separately; proof does not establish operating-system memory availability.

For every Rust string `s`, `unindent(s)` terminates without a modeled panic,
returns a valid UTF-8 String, and satisfies
`bytes(result) = U(bytes(s))`. The private flagged wrapper satisfies the analogous
`U_p` contract. `String::from_utf8(...).unwrap()` success is an obligation.
It must not be obtained by assuming that this application algorithm preserves
UTF-8. A contract about Unicode scalar sequences alone does not establish this
byte equality without the scalar-to-byte bridge.

Concrete extension contracts: `<str as Unindent>::unindent` and
`<String as Unindent>::unindent` satisfy the same exact byte/String contract;
`<[u8] as Unindent>::unindent` satisfies the byte/vector contract. The generic
`<&T as Unindent>::unindent` delegates to the underlying `T` implementation.
Any totality/contents guarantee for arbitrary user `T` is conditional on its
trait contract; the original public trait permits arbitrary implementations.
Do not silently narrow the public generic domain or impose `U` semantics on all
implementations. Concrete body proofs and generated refinement/law proofs are
separate coverage entries.

## Supporting contracts and loop relations

The following are proposed checked helper contracts. Their exact Rust signatures
may differ. A proved operational ghost recurrence is useful only when a checked
bridge connects it to the independent decomposition/minimum model above.

| Helper | Preconditions and exact postcondition |
|---|---|
| `line_end_index(s,a)` | `a <= |s|`; result `e` is in `[a,|s|]`, every byte in `[a,e)` differs from LF, and `e = |s| || s[e] = LF` |
| `leading_end_index(s,a,e)` | `a <= e <= |s|`; result `k` is in `[a,e]`, all bytes in `[a,k)` are white, and `k = e || !white(s[k])` |
| `count_spaces(l)` | returns None iff blank; Some(k) iff `k = indent(l)` and `k < |l|` |
| `common_margin(s,a)` | `a <= |s|`; exact minimum over nonblank segments after the first in `segments(s[a..|s|])`, with zero for the empty eligible set |
| `append_range(s,a,e,v)` | `a <= e <= |s|` and sufficient modeled vector-length capacity; returned bytes equal old `v@ ++ s@[a..e]`, length is old length plus `e-a` |
| `BytesExt::lines` if selected | generated fields are exactly `segments(prepare(s@))`, including all empty endpoints |

Search loops maintain both bounds and the universal predicate on the visited
prefix. Margin traversal maintains that the visited complete lines are precisely
an initial segment of all later lines, and that `found_margin/spaces` is exactly
their optional minimum: no candidate, or an attained candidate no greater than
every candidate seen. At termination, every later line has been visited.

Output traversal maintains equality of the accumulated vector to the
LF-intercalation of the visited transformed fields, with the initial-field
suppression rule already accounted for. It also maintains its source position
and the source prefix length consumed. For copying a field range `[a,e)`, the
inner invariant is `v@ = v_entry@ ++ s@[a..i]`, `a <= i <= e`.
Use a consumed-source bound, strengthened as needed for the next LF and field,
to prove each push and append stays within the original input length. A final
output-length claim alone does not justify intermediate vector growth.

`line_end + 1` is executed only when `line_end < |s|`. `line_start + spaces`
is executed only when `spaces < line_end - line_start` (or establish the
corresponding non-strict bound for a different branch). If a line counter is
incremented, prove its relation to consumed LF bytes and hence its safe bound.
Loop variants decrease in mathematical nonnegative remaining input/field
length; nested loops need their own variants. A panic-freedom proof without
termination does not establish the requested total-success contract.

## UTF-8 proof boundary

A sufficient checked argument splits valid UTF-8 at ASCII LF bytes, observes
that an initial ASCII CR is a complete code point, and shows each removed line
prefix consists only of ASCII SPACE/TAB bytes. Nonblank later lines have at
least the common margin indentation; shorter blank lines contain only removable
ASCII bytes. Retained suffixes therefore begin at UTF-8 code-point boundaries.
Concatenating valid UTF-8 fields with ASCII LF preserves validity.

Required bridge lemmas include: valid UTF-8 slices at proven boundaries; ASCII
LF split boundaries; white prefixes end at code-point boundaries; valid UTF-8
concatenation; and `valid_utf8(x) ==> valid_utf8(U_p(x))`. Their application
content must be proved. Standard-library models may state faithful contracts
for `str::as_bytes`, vector contents, `String::from_utf8` and String byte views;
they must not assume `valid_utf8(U_p(x))`. If the available string model cannot
express these facts, the string wrapper remains open while the byte core may
still be proved.

## Coverage and external assumptions ledger

Every row is an obligation; current execution status belongs to the separate
results/evidence record, not this fingerprinted specification.

| Target | Required scope |
|---|---|
| Public `unindent_bytes` | Arbitrary bytes, exact U, successful termination |
| Private byte core | Exact flagged semantics, bounds, overflow, termination |
| Public `unindent` and private string core | Exact output bytes plus proved UTF-8 conversion success |
| Three concrete extension implementations | Exact corresponding contract and any generated refinements |
| Generic reference extension | Faithful conditional delegation; no claim for arbitrary implementation behavior |
| Byte scanning, margin, append helpers | Exact helper contracts, all generated bodies and lemmas |
| Decomposition/minimum/output bridges | Checked agreement of operational ghost models with independent U |
| UTF-8 bridge lemmas | Checked preservation for this transformation |
| Original iterator release algorithm | Separate correspondence theorem if proof subject is adapted |

Inventory the actual imported contracts for slice length/indexing/subslices,
vector creation/push/extension, integer conversion, iterator operations if used,
and string conversion. State their preconditions, view/deep-model relationships,
target-dependent bounds, allocation assumptions, and unsupported observations.
External standard-library assumptions are not application proofs. No `trusted`,
admitted application lemma, false trait precondition, or unchecked application
extern contract may replace a required result.

## Semantic regression cases and review gates

Required cases include empty input, whitespace-only first line, LF/CRLF initial
newline, repeated empty lines, terminal LF, tabs counted by byte, short blank
lines, invalid UTF-8 byte API inputs, NUL and non-ASCII UTF-8. In particular:
`U(b"    a") = b"    a"`, `U(b"\n\n") = b"\n"`,
`U(b"\n \t") = b" \t"`, and
`U(b"\r\n    a\r\n\r\n    b") = b"    a\r\n\r\n    b"`.
The interior CR-only field is nonblank and forces margin zero. Preserve this
observed release behavior; do not fix it in the verification adaptation.
Idempotence is not a valid general contract.

Before accepting a proof, inspect the actual generated caller/root goals for
the exact contents and successful-return claims, including model-boundary
preconditions and all helper/trait goals. Require a fresh positive target
inventory, closed leaves, successful exit, and unchanged before/after input
fingerprints. A model definition, isolated probe, native differential test or
zero-goal translation does not discharge a public algorithm obligation.

Independent review notes will identify reviewed source/goal identities and
remaining obligations; no proof result is asserted by this initial specification.

## Pearlite model interfaces and independent review notes

`src/spec.rs` supplies the declarative relation `unindented(s,p,out)` using
existential LF-free decomposition, an attained exact minimum, and intercalation
of the transformed fields. Its secondary `source_unindented(s,p,out)` relation
describes the complete ordered sequence of retained original source positions.
`selection_trace` records the explicit position witness for a loop: every output
byte has the indicated source value, positions strictly increase, and every
retained source position below the processed bound occurs. Completeness is
required; a mere subsequence relation would permit returning an empty vector.
The source-position relation and the decomposition relation have the same
intended semantics, but their equivalence remains a checked bridge obligation.
Do not report a proof of one relation as a checked theorem of the other without
that bridge.

Independent standard-model review accepts these UTF-8 encoding facts as narrow
candidate assumptions about the frozen library's `char::to_utf8` model:
an ASCII scalar encodes as its single byte, and every encoded byte of a non-ASCII
scalar is at least 128. The scalar domain must respect the existing valid-char
invariant; a byte/scalar equality witness avoids unchecked narrowing casts.
These facts concern standard encoding only, not this application's output.
They do not establish the required application preservation lemma, conversion
success, or wrapper contract. The final assumptions ledger must identify their
actual declarations and use sites if adopted.

### Mathematical review of the source-position characterization

This is an independent specification review, not a checked Creusot bridge:

1. Every later LF-delimited field of the original source has a unique start
   `a > 0` with `s[a-1] = LF`. Removing the initial CR does not change any later
   field's contents or indentation. A `later_candidate(s,a,k)` exists precisely
   when that field is nonblank, and its unique `k-a` is its indentation:
   whitespace before `k` contains no LF, and `s[k]` is neither whitespace nor LF.
   Thus the candidate minimum in `source_margin` is the decomposition margin.
2. For a non-LF byte, `source_line_start` identifies its unique containing field.
   First-field bytes are retained, except the initial CR of CRLF. In every later
   field exactly the bytes at offsets at least `m` are retained. This is precisely
   the suffix after dropping `min(m, field length)` bytes; it holds even for blank
   fields shorter than the margin.
3. All LF bytes are retained except the first LF when suppression is requested
   and the input begins with LF or CRLF. This is exactly the separator removed
   by dropping the initial empty field. Every remaining separator occurs in
   source order, preserving empty and terminal fields.
4. Strictly increasing source positions, exact byte values, and completeness
   uniquely specify the ordered retained subsequence. They permit neither an
   omitted retained byte, an extra byte, a duplicated position nor a permutation.
   Consequently the source relation describes the same mathematical output as U.

A closed theorem for `source_unindented` therefore has a substantial exact
functional contract in its own right. Its raw checked statement is still that
relation; this mathematical review must not be reported as a machine-checked
equivalence theorem to `unindented`. The formal bridge remains separately visible.

Latest source-contract review observes a two-pass adapted byte core: indexed
margin discovery followed by a bytewise retention scan with a ghost source
position trace. This is a further adaptation from the earlier line-by-line
explicit-index candidate. Public byte and string contracts require exact
`source_unindented`, a non-growth bound, and termination checks; loop variants
are explicit. The source trace bounds intermediate output length by bytes
processed. Concrete byte/str/String extensions carry corresponding contracts.
The unrestricted generic reference extension remains present natively but is
excluded from Creusot selection; it has no universal totality guarantee for
arbitrary downstream implementations. These observations review source
obligations only and do not assert that their generated goals have closed.
