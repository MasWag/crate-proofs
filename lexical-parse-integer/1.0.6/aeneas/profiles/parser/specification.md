# Scalar loops and unsigned-byte parser adaptations

The independent scoped contracts are in
[SCALAR-SPECIFICATION.md](../../../SCALAR-SPECIFICATION.md), extending the
main [specification](../../../SPECIFICATION.md). `proofs/ScalarSpecs.lean`
defines structurally recursive independent scans over mathematical byte values
and separate complete and partial parser front ends. `proofs/DigitSpecs.lean`
defines ASCII digit conversion independently of implementation normalization.
This document states obligations, not managed acceptance or release equivalence.

The unsigned checked decimal loop accepts an arbitrary U32 entry
accumulator. For a byte slice `bytes`, entry value `v`, and original offset `j`,
the contract requires total Aeneas success and exact correspondence of its
normal Rust result to `checkedU32Scan (map byteValue bytes) v.val j.val`.
The entry accumulator is not restricted to zero. The zero-offset wrapper uses
`j=0`. To justify incrementing an offset counter, require the representational
bound `j + bytes.length <= usize::MAX` in unbounded arithmetic. This bound
is a private state/representation premise, not a valid-digit premise.

The model checks whether each byte is a decimal digit before evaluating its
next magnitude. A nondigit returns `InvalidDigit(j+k)` even if multiplying the
current accumulator would overflow. A digit causing `10*v+d > 2^32-1` returns
`Overflow(j+k)` at that first excessive prefix. Otherwise it continues.
Empty input returns the entry value. A parse error must be a Rust `Err` inside
successful Aeneas execution, not Aeneas failure. Implementations map the model's
independent `ScanResult` constructors to actual error constructors explicitly.

Signed I32 checked-loop contracts use the same first-event rule with entry sign
discipline: nonnegative accumulation has magnitude bound `2^31-1`, while
nonpositive accumulation has bound `2^31` and uses `Underflow` on the first
excessive magnitude. A successful negative-path result is minus the mathematical
magnitude. Private entry magnitudes need not be zero. The same offset bound
applies. These loop obligations do not establish a signed parser front end.

For U8, the checked scan uses bound 255. The unchecked initial region must agree
with that mathematical scan when entered at zero for at most two bytes; this
length premise belongs only to the private optimization. Complete and partial
front-end contracts cover arbitrary byte slices without a valid-digit or length
restriction. Both accept one optional initial plus and report `Empty` at the
post-sign cursor for empty or sign-only input. Minus is an ordinary nondigit.
The complete result agrees exactly with `completeU8`; invalid bytes are errors.
The partial result agrees exactly with `partialU8`; the first invalid byte ends
parsing successfully without consuming it, and even a zero-digit prefix returns
zero with the post-sign consumed count. End of input returns the original input
length as consumed count. Both modes report the first overflow before any later
invalid byte. Counts and error indices always refer to the original input.

Byte conversion has its own total contract for every U8 and radix 2 through 36:
`char_to_digit_const` returns exactly the independent `DigitSpecs.digit` option,
with ASCII `0..9`, `A..Z`, and `a..z` giving case-insensitive values 0 through 35
when below the radix, and `None` otherwise. This does not extend the decimal
scan or front-end contracts to other radices.

Loops must derive from the release's scalar macro control/arithmetic order.
Record outlining, explicit accumulator/radix/offset substitutions, error-type
identity, and replacement of the no-skip iterator by slices. Front ends select
the unsigned-byte, decimal, standard-format behavior and preserve the two-digit
unchecked prefix before the checked remainder. Source comparison and reviewed
dispatch selection are separate from formal Rust-to-Rust equivalence. Proving
these adapted bodies does not establish the original generic public parsing
traits, custom syntax, other widths, or block-loop integration. Do not map an
adapter result as full release `algorithm_complete` or `algorithm_partial`
correctness without a separate equivalence argument.
