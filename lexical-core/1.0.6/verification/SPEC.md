# lexical-core 1.0.6 specification

Specification design: Astra. Generated-body proof implementation: Sol. The primary
agent reviews contracts, extraction commands, evidence and coverage claims. This
document states obligations; it does not certify that any obligation has passed.

## Subject and observations

The subject is the crates.io lexical-core 1.0.6 archive identified by
`source.lock.json`, restored unchanged under `.work/source`. Its default features
enable integer and floating-point parsing and writing, with `std`. Each proof
must record the actual features, target, dependency lock, Rust extraction input,
and unchanged Aeneas revision used. A narrower extraction does not verify the
other default features. Platform integer widths follow the recorded target.

The six free functions in release `src/lib.rs` are `parse`, `parse_partial`,
`parse_with_options`, `parse_partial_with_options`, `write`, and
`write_with_options`. Parsing forwards through `FromLexical` or
`FromLexicalWithOptions`; writing forwards through `ToLexical` or
`ToLexicalWithOptions`. The concrete implementations forward again to the
corresponding lexical-parse/write-integer/float crate. Both dispatch steps and
the selected dependency bodies matter for an algorithm claim.

Inputs to parsing are arbitrary byte slices; no UTF-8 or ASCII precondition is
imposed on the complete error-inclusive contract. Positions count original
bytes. Parsing observations are the exact Rust `Ok` value and partial count, or
the exact Rust `Err` variant and position. A Rust error is an ordinary returned
value, distinct from Aeneas failure, panic or divergence.

Writing observations include the returned byte slice, its length and prefix
position within the input buffer, and the updated borrowed buffer. In the Aeneas
representation, any generated backward function is part of the observation:
replacing the returned subslice must update the corresponding prefix of the
caller buffer. There is no additional promise here that scratch bytes beyond
the returned slice are unchanged; release documentation makes no such promise.

Use total-success contracts:

```
pre input -> exists out, actualGeneratedCall input = Aeneas.Result.ok out
                         /\ independentRelation input out
```

A precondition that assumes the call already has the desired value cannot close
an algorithm obligation. It is permitted only in an explicitly conditional
facade-composition theorem, described below.

## Independent integer relation

For radix `r`, `2 <= r <= 36`, decode ASCII `0..9`, `a..z`, `A..Z` to values
`0..9`, `10..35`, `10..35`, accepting only values below `r`. All other bytes are
nondigits. Define

```
value_r [d0,...,d(n-1)] = sum_i d(i) * r^(n-1-i)
value_r [] = 0
```

This is arithmetic over unbounded natural numbers, with no wrapping. Unsigned
width `w` admits values `0..2^w-1`; signed width `w` admits
`-2^(w-1)..2^(w-1)-1`. A negative sign negates the magnitude, including zero.

For the initial STANDARD decimal parser contract, consume at most one initial
`+`, or `-` for signed types. For unsigned types `-` is a nondigit. Let `s` be
the cursor after the optional sign. No whitespace is ignored.

1. If the input ends at `s`, return `Empty(s)`.
2. Scan decimal digits from `s`, using the mathematical magnitude. The first
   digit at original index `j` for which the inclusive prefix exceeds the
   permitted magnitude returns `Overflow(j)` for a nonnegative input, or
   `Underflow(j)` for a negative input. This precedes a later nondigit.
3. A nondigit at `k` before any overflow makes complete parsing return
   `InvalidDigit(k)`. Partial parsing returns the signed value of `[s,k)` and
   count `k`.
4. At end of input, return the signed value, and the input length for partial
   parsing.

Step 3 deliberately allows a zero-length digit run for the delegated standard
partial integer parser: for example `?` has value/count `(0,0)` and `+?` has
`(0,1)`. This behavior is documented by the existing sibling investigation in
`lexical-parse-integer/1.0.6/SPECIFICATION.md`; it must be confirmed against the
resolved dependency selected here. The empty/sign-only cases remain errors.
If a dependency version or feature profile changes this behavior, record and
resolve the discrepancy rather than silently changing the relation. This is
an exact compatibility obligation, not a claim that the API requires a digit
in every successful partial result.

For a successful partial result containing at least one digit, complete parsing
of the consumed prefix must yield the same value. A successful complete parse
must agree with a partial parse consuming the entire input. These are derived
obligations, not replacements for the exact numeric relation.

For integer writing, define `decimal(0) = [ASCII 0]`. For positive `n`,
`decimal(n)` is the unique nonempty list of decimal digits with no leading zero
and mathematical value `n`. For signed negative `n`, its representation is
`[ASCII -] ++ decimal(abs(n))`; otherwise it is `decimal(n)`. In particular,
the minimum signed integer uses the mathematical absolute value, not an
overflowing signed machine negation.

Given a buffer at least the documented `N::FORMATTED_SIZE` for a default writer,
the returned prefix must be exactly this representation and have its exact
length. A theorem with this documented capacity premise does not cover smaller
buffers even if the particular value might fit. For custom options, establish
an independently justified sufficient capacity; do not assume the default
constant suffices for arbitrary float precision or exponent break points.

### Compact decimal u8 specialization

For the compact writer investigation, specialize to `u8`, radix 10, STANDARD
format, and no custom sign requirement. For every mathematical `0 <= n <= 255`,
let `D = decimal(n)` as defined above and `k = length(D)`. Equivalently, `D` is
the unique ASCII digit list with value `n`, `1 <= k <= 3`, and no leading zero
unless `D = [ASCII 0]`. This relation does not use the writer as an oracle.

For an arbitrary initial byte buffer `B` with `length(B) >= 3`, the actual
compact helper should terminate successfully with count `k` and updated buffer

```
B' = D ++ drop k B.
```

This stronger suffix-preservation property is scoped to the compact release
body: its scratch digits live in a separate local 128-byte array and its only
caller-buffer write is the final `copy_to_dst`. It is not assumed for other
writers merely because they share the public API. A helper theorem under the
weaker sufficient-capacity premise `length(B) >= k` is also valid; the fixed
three-byte premise is convenient for the public decimal-u8 contract.

At the public borrowed-slice boundary, if the generated output is `(S, back)`,
require `S.val = D` and, for every replacement slice `R` with length `k`,

```
(back R).val = R.val ++ drop k B.val.
```

Taking `R = S` yields the final buffer after ending the borrow. Quantification
over same-length replacements states that subsequent writes through the
returned mutable slice update exactly the corresponding prefix; slice contents
alone do not establish this property. The return count/length must be the
numeric digit count, including one digit for zero, not the scratch-array index.

Any specialization or loop outlining must preserve the scratch-index bounds,
division/remainder semantics and exact copy range. A generated-body theorem
about adapted code is reported as adapted compact-u8 coverage. It closes no
unchanged-release facade or dependency row without a separately checked
connection to those bodies; native exhaustive checks over 256 values remain
separate evidence of correspondence.

## Independent floating-point obligations

The first arithmetic target is finite STANDARD decimal input, for `f32` and
`f64` separately, using default non-lossy parsing. For a decimal significand
with integer digits `a`, fractional digits `b`, and signed exponent `e`, define
the exact real value as

```
(-1)^sign * (value_10(a) * 10^length(b) + value_10(b))
          * 10^(e - length(b)).
```

Omitted fractional parts and exponents have their usual zero-length/zero
values. The grammar requires at least one significand digit and, when an
exponent marker is present, at least one exponent digit. Acceptance of other
lexical forms and error precedence must be stated separately; this arithmetic
subset is not an all-input parser contract.

The numeric target is IEEE binary round-to-nearest, ties-to-even of this exact
value, including subnormals, signed zero, and overflow to infinity. Specify
results by IEEE bit patterns where zero sign matters. Preserve the lexical sign
separately from the real value: a negative exact zero or a negative value that
rounds to zero produces negative zero. The rounding definition
must be independent of the Rust fast path and fallback algorithms. A proof
restricted to finite rounded results must say so and leaves overflow open.

Release inspection supports this target without proving it: the resolved
lexical-parse-float 1.0.6 `src/lemire.rs::compute_float` contains explicit
ties-to-even and infinity branches, and `src/parse.rs::parse_complete` returns
the converted number as `Ok`, applying the sign after conversion. Consequently,
decimal overflow is a successful infinity result in this target, not the integer
parser's `Overflow` error. Its fast path uses native floating-point arithmetic;
the selected target/library model must supply the intended IEEE rounding and
subnormal semantics. No guarantee under externally altered floating-point
control state is claimed by the mathematical relation alone.

For partial finite parsing, prove the same rounded value and exact consumed
prefix under an explicitly stated decimal-prefix grammar. A longest-valid-prefix
statement alone must not predetermine how incomplete exponent syntax is handled.
The full float API additionally needs exact errors and indices, incomplete
exponents, special values, case rules, empty input, arbitrary invalid bytes,
and partial stopping semantics. Those are separate open grammar obligations,
not assumed consequences of the finite arithmetic theorem. Lossy parsing and
custom tokens are separate option-dependent contracts.

For default float writing, require a well-formed decimal or documented special
token and exact returned length/prefix. For each finite input, the mathematical
rounding operation applied to the emitted decimal must recover the input IEEE
value, including zero sign. This independent roundtrip relation must not be
defined by executing lexical-core's own parser. NaN output is specified by NaN
classification, not preservation of an unspecified payload. Positive and
negative infinities must preserve their classification and sign.

If claiming shortest formatting, additionally prove minimal significant-digit
count among decimal representations that round to the same value, under the
selected options. Shortest significant-digit count is distinct from shortest
total byte length: exponent notation and a required decimal point can change
total length. Exact token spelling, fixed/scientific selection, precision,
tie-breaking and formatting flags require a separate selected-option grammar.
A roundtrip-only theorem must be reported as such, not as full formatter
correctness or shortest-output correctness.

## Facade and configuration contracts

For all six generic free functions, an exact forwarding theorem may prove
equality to the actual corresponding generated trait method with the same
input, options and const FORMAT. For writers this equality includes the full
returned mutable-borrow representation and its backward function. Such equality
preserves outcomes, including failure; it is a structural delegation theorem,
not a total-success numeric theorem.

A useful conditional total-success theorem is:

```
(exists out, actualTraitCall input = .ok out /\ R input out)
  -> exists out, actualFacade input = .ok out /\ R input out
```

The theorem must label its dependency-success premise. It closes only facade
composition. To close a concrete public algorithm row, instantiate the trait
with its actual numeric implementation and discharge that premise using
audited dependency-body theorems with the independent integer/float relation.
A generated trait field supplied as a Lean parameter is not an axiom, but its
arbitrary semantics still prevent an unconditional numeric coverage claim.

### Trait-bound-erased facade adaptation

The first original-release facade extraction retains unused `Number`
supertrait fields, including `AsPrimitive` casts to floating-point types. In the
selected unchanged translator these become undeclared `F32`/`F64` types and
prevent the generated release model from compiling. An extraction file
containing the six facade bodies is therefore not accepted release evidence.

The explicit derived Rust input `verification/facade/src/lib.rs` defines four
method-only traits and copies the six release free-function definitions. It
retains the required method signatures, associated Options types, const FORMAT,
lifetimes and mutable-reference returns. It removes unused `Number` and
`FormattedSize` supertraits and `ParseOptions`/`WriteOptions` associated-type
bounds. Explicit `Sized` preserves sizing needed by method signatures. The
harness has no built-in numeric implementations and enables no default feature
set of lexical-core; it depends on lexical-util 1.0.7 with default features off.

`scripts/check-facade-adaptation.py` checks exact free-function text and required
method signatures against locked release input and the pinned lexical-util API
macro source. This is a source-correspondence check, not a semantics theorem.
Review supports projecting each release dictionary to the same methods after
discarding unused fields, but no checked Rust-to-Rust or generated-model
equivalence theorem currently establishes that projection. In particular,
unchanged function text refers to different, deliberately weaker trait types.

The six equality and six conditional-success contracts apply to the generated
`lexical_core_facade_harness` definitions when this input is selected. They
retain the same observable relations, including complete writer backward
functions, but must be mapped and reported as adapted facade coverage. They do
not close the original-release generic-dispatch row or any concrete numeric
row. No replacement meaning for floating-point operations and no Aeneas or
Charon modification is authorized by this adaptation.

Options builders and accessors must specify their actual stored fields and
validation outcomes for all representable raw states available through the
public interface. An integer `no_multi_digit` option is an optimization choice:
equality of numerical results, errors and counts between its settings requires
parser-level composition, not just an accessor theorem. Re-exported options and
format-builder results are auxiliary configuration coverage only.

Custom FORMAT validation, separator/sign policies, radices, lossy float parsing,
special tokens, custom writer precision, and optional `f16`/`bf16` support each
require an explicit additional contract. Default/compact feature equivalence
must be proved or reported separately; matching native samples is not a proof.

## Priorities and coverage ledger

Probe extraction of all four core families immediately. Then prioritize an
unconditional STANDARD decimal integer operation if reachable, followed by its
matching parse/write operation and composition. General generic forwarding is
useful intermediate work, but does not replace a blocked core family. Floating
rounding and shortest formatting remain explicit requested obligations even
when the unchanged translator does not support their bodies.

The status below is a specification baseline: every row is open until a named
accepted theorem and evidence record discharges it. Record actual extraction
blockers and proof results in the profile results without interpreting the
existence of this document as evidence.

| Obligation | Required accepted evidence | Initial status |
| --- | --- | --- |
| Integer complete parse | Actual facade and dependency bodies; exact value/error/position; total success | Open |
| Integer partial parse | Same, with exact consumed byte count on arbitrary input | Open |
| Integer write | Actual bodies; canonical decimal prefix and length; borrowed-buffer relation; total success under capacity premise | Open |
| Float complete parse | Actual bodies; independent correctly rounded value plus selected grammar/error relation | Open |
| Float partial parse | Same with exact consumed prefix and malformed-prefix semantics | Open |
| Float write | Actual bodies; independent numeric roundtrip, selected formatting grammar and buffer relation | Open |
| Float shortest/precision guarantees | Separate minimality/rounding theorem for selected options | Open |
| All integer widths and float types | Explicit type instantiations and target bounds; no inference from one type | Open |
| Six generic free-function dispatches | Exact generated-body forwarding and conditional total-success transfer | Open; auxiliary |
| Concrete trait dispatches | Actual numeric impl delegation and discharged dependency contracts | Open |
| Options/format construction and access | Actual constructor/accessor state and validation relations | Open; auxiliary |
| Custom FORMAT/options and optional features | Explicit configuration grammar, semantics, validation and capacity | Open |
| Source adaptation equivalence | Preserved original source; reproducible diff; separately assessed release equivalence | Not established |

## Trust and acceptance boundaries

Proofs must target generated bodies, not hand-written replacements of application
logic. Generated Lean compilation, finite native tests, arbitrary-trait facade
theorems, and mathematical model lemmas are separate kinds of evidence. They
must not be counted as unconditional parser or formatter proofs.

The accepted chain must include regenerated-model comparison, theorem inventory,
transitive axiom audit allowing only `propext`, `Classical.choice`, and
`Quot.sound`, and before/after input fingerprints. The Rust-to-Lean translator
and selected library models remain trust boundaries. An unsupported float,
pointer, borrow, or trait construct is an extraction limitation, not proof that
the Rust algorithm is incorrect or unprovable.

The user freezes Aeneas, not automatically the application source. Any source
adaptation must remain a separate derived input with original and adapted
hashes. A proved adapted implementation and a reviewed correspondence argument
do not establish formally checked Rust-to-Rust equivalence. Existing sibling
integer proofs may supply proof patterns or explicitly matched adapted
dependency results, but cannot silently replace the release dependency used by
lexical-core or close its release-source obligations.
