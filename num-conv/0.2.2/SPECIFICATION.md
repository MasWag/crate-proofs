# num-conv 0.2.2: independent functional specification

Specification responsibility: Astra; proof implementation responsibility: Sol;
acceptance and evidence review: the primary agent. These contracts precede proof
implementation and must not be weakened to match extractor or prover limitations.
This document specifies required coverage, not achieved verification.

## Source and scope

The subject is the crates.io `num-conv` 0.2.2 release, particularly `src/lib.rs`.
Source identity and extraction configuration are recorded separately by the
verification runner. The release provides five public conversion methods:
`Widen::widen`, deprecated `Extend::extend`, `Truncate::truncate`,
`Truncate::saturating_truncate`, and `Truncate::checked_truncate`.
The first two and the last three are each generic dispatchers over sealed
implementations. The implementation ledger below is exhaustive for this release.

The extraction harness `verification/api.rs` includes the unchanged release
`src/lib.rs` by path as its `release` module and supplies 180 concrete, single-call
wrappers invoking those public methods. Root trait reexports preserve the release
prelude's `crate::{...}` references. This packaging forces extraction of the real
concrete trait dictionaries and public dispatch chains; it does not substitute
mathematical implementations for release bodies. The source correspondence checker
compares the wrapper ledger and direct calls with the release macro declarations.
Source-byte identity and this inspected packaging correspondence are part of the
trust boundary, not a formal proof of equivalence between Rust crate packaging
configurations. Accepted evidence must disclose this harness adaptation.

The three public `*Target` traits carry no additional executable methods of their
own. `prelude` reexports the three conversion traits. The private `Integer` trait
and marker implementations constrain the available integer types. Their presence
and the public dispatch-to-sealed-implementation connection require inspection;
they must not be counted as additional numeric algorithms.

## Mathematical model and full domains

For an integer type T, let w(T) be its bit width, and val_T(x) its mathematical
integer value. For fixed types the width is the suffix 8, 16, 32, 64, or 128.
For `usize` and `isize`, the width is the extraction target's pointer width p.
For every supported pointer width p >= 16, define:

* unsigned: L(T) = 0 and H(T) = 2^w(T) - 1;
* signed: L(T) = -2^(w(T)-1) and H(T) = 2^(w(T)-1) - 1.

Every contract quantifies over **all** values of its source integer type, including
zero, extrema, negative signed values, and values outside the destination range.
Representability in the source type is intrinsic to its type; there is no extra
caller precondition. No fit-in-destination premise is allowed for a narrowing
operation. No assumption that an operation succeeds may replace its success proof.

The mathematical specification is width-parametric. A checked proof for one
extraction target does not establish extraction or generated-body correctness for
another pointer width. Coverage claims must identify the checked target. Wider
pointer types do not create undeclared API pairs: in particular `u32 -> usize`,
`usize -> u32`, `i32 -> isize`, and `isize -> i32` are absent even on a 64-bit target.
There are no signed-to-unsigned or unsigned-to-signed conversions in this release.

## Required total-success contracts

Let F be the actual generated function for the selected public method and concrete
source/destination pair, with all its generated trait arguments instantiated by
the release's real implementations. For every source value x, prove

    exists out, F x = Result.ok out and P(x, out).

`Result.ok` is the extraction execution result, not Rust's `Option`; the checked
method's successful output may itself be `None`. An equivalent unconditional
equation to `Result.ok` of a specified result is acceptable. A sealed-body theorem
alone needs a checked connection to the public dispatcher before it establishes
public API coverage. A generic dispatcher lemma may assume its callee contract,
but each claimed concrete public instance must discharge that premise.

### Widen and deprecated extend

For each declared pair S -> T, require

    val_T(out) = val_S(x).

This specifies exact preservation of the mathematical value, including negative
values (sign extension) and unsigned values (zero extension). The identity cases
are included. The destination range contains the entire source range for every
listed pair. Deprecation does not remove `extend` from required coverage.

### Truncate

Let n = val_S(x), b = w(T), and let `a mod m` mean the nonnegative Euclidean
remainder in [0,m), including when a is negative. Require:

    unsigned T: val_T(out) = n mod 2^b
    signed T:   val_T(out) = ((n + 2^(b-1)) mod 2^b) - 2^(b-1).

Equivalently, the output is the unique integer in [L(T),H(T)] congruent to n
modulo 2^b. This is preservation of the low b bits, with two's-complement signed
interpretation. It is not remainder with division truncated toward zero.
For example, i16(-129) -> i8 gives 127; i16(128) -> i8 gives -128;
i16(-1) -> i8 gives -1; u16(256) -> u8 gives 0.

### Saturating truncate

Require

    val_T(out) = max L(T) (min H(T) (val_S(x))).

Thus below-range inputs yield the destination minimum, above-range inputs yield
its maximum, and in-range inputs preserve their exact value. Both boundaries are
inclusive. This independent interval projection specification does not refer to
the implementation's casted comparisons or branch order.

### Checked truncate

Require both directions of the range test, including successful value preservation:

    if L(T) <= val_S(x) <= H(T):
      exists y, out = Some y and val_T(y) = val_S(x)
    otherwise:
      out = None.

An equivalent characterization is `out = None` iff the value is out of range and
`out = Some y` iff val_T(y) = val_S(x). Merely proving correctness conditional on
`Some`, or safety without a result characterization, is insufficient.

## Complete concrete API coverage ledger

Each destination in the next table denotes **two** independent concrete public
contracts, one for `Widen::widen` and one for `Extend::extend`.

| Source | Every declared destination for widen and extend |
| --- | --- |
| u8 | u8, u16, u32, u64, u128, usize |
| u16 | u16, u32, u64, u128, usize |
| u32 | u32, u64, u128 |
| u64 | u64, u128 |
| u128 | u128 |
| usize | usize |
| i8 | i8, i16, i32, i64, i128, isize |
| i16 | i16, i32, i64, i128, isize |
| i32 | i32, i64, i128 |
| i64 | i64, i128 |
| i128 | i128 |
| isize | isize |

There are 36 pairs, giving 36 widen contracts and 36 extend contracts.

Each destination in the next table denotes **three** independent concrete public
contracts: `Truncate::truncate`, `Truncate::saturating_truncate`, and
`Truncate::checked_truncate`.

| Source | Every declared destination for the three truncation methods |
| --- | --- |
| u8 | u8 |
| u16 | u8, u16 |
| u32 | u8, u16, u32 |
| u64 | u8, u16, u32, u64 |
| u128 | u8, u16, u32, u64, u128 |
| usize | u8, u16, usize |
| i8 | i8 |
| i16 | i8, i16 |
| i32 | i8, i16, i32 |
| i64 | i8, i16, i32, i64 |
| i128 | i8, i16, i32, i64, i128 |
| isize | i8, i16, isize |

There are 36 pairs, giving 108 truncation-family contracts and **180 concrete
method contracts total**. Of these, 30 mention pointer types (12 widening/extension
and 18 truncation-family contracts). The remaining 150 involve only fixed widths.
No nonidentity fixed-width integer conversion algorithm may be omitted while
claiming complete coverage of this ledger.

## Acceptance and bug-review obligations

Map each concrete method above to its audited theorem, generated implementation,
and checked public-dispatch connection. Helper lemmas and five generic dispatch
lemmas are not substitutes for the 180 instantiated functional obligations.
Preserve this requested ledger if any entry remains blocked and identify that
entry separately from achieved coverage.

Native tests should exercise both signed range boundaries, the neighboring
out-of-range values when representable, source extrema, zeros, and identity cases.
They supplement the proofs and do not establish universal contracts. Any claimed
release bug needs a native reproduction against the original release and a clear
violated contract; extractor limitations are separate verification gaps.

Initial source review found no mismatch between the five stated behaviors and
the release's same-signedness pair selection or conversion bodies. This is a
source-review observation, not a formal proof or an exhaustive testing result.
