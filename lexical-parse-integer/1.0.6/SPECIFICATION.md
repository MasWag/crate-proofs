# Integer parsing specification

Specification responsibility: Astra. Generated-body proof implementation: Sol.
The primary agent reviews release correspondence, proof dependencies, commands,
and coverage. This document defines obligations, not completed proofs. A theorem
about the mathematical model alone is not a theorem about the Rust parser.

## Source and observable result

The subject is the checksum-pinned crates.io `lexical-parse-integer` 1.0.6
release, including its resolved `lexical-util` dependency. The release API in
`src/api.rs` implements complete and partial parsing, with and without options,
for `u8/u16/u32/u64/u128/usize` and `i8/i16/i32/i64/i128/isize`. Platform-sized
integer bounds depend on the recorded extraction target. Input is arbitrary
bytes, not assumed UTF-8. Positions and consumed lengths count original bytes.

A total-success contract has the form
`exists out, extracted_call input = Aeneas.Result.ok out /\ relation input out`.
Here `out` may itself be a Rust `Err`. Returning a specified parsing error is
normal successful execution; Aeneas failure, panic, or divergence is not.
The relation compares the exact integer, consumed length, or error variant and
position. It does not assume the parser returned successfully.

## Independent arithmetic model

For radix `r` in `2..36`, define `digit_r(c)` by ASCII ranges: `0..9` have
values `0..9`, and `A..Z` and `a..z` have values `10..35`; a character is a
digit exactly when its value is less than `r`. All other bytes are nondigits.
For digits `d[0] .. d[n-1]`, define
`value_r(d) = sum (d[i] * r^(n-1-i))`, with empty value zero.
Equivalently the independent list fold starts at zero and maps `(v,d)` to
`r*v+d` over unbounded natural numbers. No machine wrapping occurs in this model.

For unsigned width `w`, the admissible range is `0..2^w-1`. For signed width
`w`, it is `-2^(w-1)..2^(w-1)-1`. A parsed negative magnitude `m` denotes
the mathematical integer `-m`, including zero; positive values denote `m`.
Every accepted prefix must stay within the corresponding magnitude limit.
The first digit whose inclusive prefix exceeds that limit determines the
overflow position. The negative case uses `Underflow`, the positive case
`Overflow`. This definition handles the asymmetric signed minimum exactly.

## Standard-format contract

The initial proof target is the standard decimal format. Other formats remain
explicit obligations below. Parse at most one initial `+`, or one initial `-`
for signed target types. No whitespace is ignored. For unsigned targets `-`
is an ordinary nondigit. Let `s` be the byte offset after the optional sign.

1. If input ends at `s`, return `Empty(s)`.
2. Otherwise scan the maximal digit run starting at `s`. At each digit, check
   the unbounded magnitude against the target bound. If the first excessive
   prefix ends at original index `j`, return `Overflow(j)` or `Underflow(j)`.
   Such an earlier overflow takes precedence over a later nondigit.
3. If a nondigit occurs at `k` before overflow, complete parsing returns
   `InvalidDigit(k)`. Partial parsing returns the signed fold of `[s,k)` and
   consumed length `k`, subject to the zero-digit rule below.
4. If the run reaches the end, return the signed fold; partial parsing also
   returns the original input length.

For the zero-digit case, native probes of both the default and
`format,power-of-two` profiles return `Ok((0, 0))` for `b"?"` and
`Ok((0, 1))` for `b"+?"`. The standard partial-parser relation permits this
zero-valued empty digit prefix, with consumed count `s`. The required-digit
branch alone does not justify an `Empty` prediction: the iterator has already
visited the invalid byte when its current count is inspected. The empty
input/sign-only cases in step 1 remain errors. A stronger nonempty-digit-prefix
contract is a separate specification question, not a confirmed bug or a
feature discrepancy. See the [native probe](verification/behavior/README.md).

For every successful partial parse containing digits, its consumed prefix must
parse completely to the same value under the same standard format. Successful
complete parsing must agree with partial parsing consuming the full input.
These are additional derived API obligations, not substitutes for exact values.

The [scoped scalar and caller contracts](SCALAR-SPECIFICATION.md) split these
obligations into checked steps, scans, sign handling, iterator relations and
block composition without narrowing the public parser contract.

## Optimization obligations

The option `no_multi_digit` is a performance choice, not a numeric or grammar
choice. Both settings must return exactly the same Rust result, including error
indices and partial consumed lengths. `compact` is likewise an implementation
feature; equivalence requires a separate checked build comparison or proof.

For little-endian packed bytes `b[0]..b[k-1]`, `k=4` or `8`, the digit
recognizer must be true iff every byte has `0 <= b[i]-48 < r`, for `2<=r<=10`.
Under that premise, the block decoder must return `value_r(map (b-48) b)`.
Packed-word lemmas must account for cross-byte carries and borrows and machine
wrapping. Block decoder correctness alone does not establish parser correctness:
the caller must prove the premise, target-width cast safety, iterator advancement,
and composition with prior digits. Checked and unchecked scalar loops must
preserve the same independent fold and exact original-byte cursor. Any unchecked
region must prove its range bound rather than assume that no overflow occurred.

## Radix and format extension obligations

`power-of-two`, `radix`, and `format` change the supported configuration surface.
An options API must reject invalid format encodings with the documented format
error before parsing input. A core-algorithm theorem assuming a valid format
does not cover that API validation. `Options` stores only `no_multi_digit`;
its `from_radix` helper does not itself choose the parsing radix.

For supported radices the arithmetic model above is unchanged. Custom syntax
must be modeled separately from arithmetic, using original byte indices:

| Syntax component | Required observable relation |
| --- | --- |
| Sign restrictions | Forbidden `+` returns `InvalidPositiveSign`; required absent sign returns `MissingSign`, at the relevant original cursor. |
| Required digits | Count actual numeric digits, separately from signs, separators, prefix and suffix bytes. |
| Leading zeros | Reject a prohibited leading zero followed by another digit; a permitted single zero consumes that zero. |
| Base prefix | Match the configured prefix after `0` with its configured case rule; retain original byte offsets and enforce following digits. |
| Base suffix | A recognized terminal suffix contributes to consumed length but not numeric value; an unrelated invalid byte must not consume a following byte. |
| Digit separators | Respect configured leading, internal, trailing, and consecutive policies; accepted separators contribute to byte consumption but not the fold. |

This table is a requirements inventory, not a fully mechanized grammar or a
coverage claim. Before proving a custom format, state its precise lexical
grammar and error precedence independently of the iterator implementation.
In particular, do not encode suspected cursor defects as the desired contract.
Source inspection identified single-zero partial-count and nonterminal-invalid
suffix-handler candidates; native reproductions and findings belong in separate
evidence. They do not affect the standard-format arithmetic definition.

## Coverage ledger and acceptance

The following rows track the original release and public parser obligations. They
remain open; adapted-body results are recorded separately below.

| Obligation | Required evidence | Release status |
| --- | --- | --- |
| Actual standard complete parser | Generated-body theorem, exact value/error, termination | Open |
| Actual standard partial parser | Generated-body theorem, value/count/error, termination | Open |
| Signed parsing and minimum bound | Negative accumulation and underflow-index theorem | Open |
| Unsigned parsing and maximum bound | Overflow-index theorem | Open |
| All integer widths, including platform widths | Explicit selected instantiations and bounds | Open |
| Scalar checked/unchecked loop | Fold invariant, cursor relation and range discharge | Open |
| Four/eight-digit fast paths | Packed-byte recognition, decoding and caller composition | Open |
| Options independence | Equality for both settings through actual parser | Open |
| Public API forwarding and format validation | Actual entry-point theorem | Open |
| Nondecimal radices | Explicit feature/radix scope and generated-body theorem | Open |
| Custom syntax and separators | Independent grammar, exact error and count relations | Open |
| Feature/profile equivalence | Named build inputs and checked relation | Open |

The historical accepted default profile covers decimal-specialized four- and
eight-byte recognition and decoding on adapted bodies; its [results](aeneas/profiles/default/results.md)
record the accepted run and scope. The following profiles have locally checked theorems. Consult their results
files for managed run status:

| Profile | Locally checked scope | Release correspondence or remaining work |
| --- | --- | --- |
| Radix | Four/eight-byte recognition and decoding for radices 2 through 10 | Explicit radix replacement is source checked; Rust-to-Rust equivalence remains open. |
| Caller | Safe decimal four/eight-byte caller adaptations, including value and cursor behavior | Original pointer and iterator callers are not proved equivalent; native differential checks are separate. |
| Parser | Complete and partial standard decimal u8 and i8 on arbitrary byte slices in adapted front ends; scoped u8/u32/i32 scalar loops; lexical-util byte-to-digit conversion for radices 2 through 36 | Front end and iterator adaptation are reviewed, and loop transformations are source checked; formal equivalence to the release remains open. Other widths and formats and block integration remain open. |
| Sign | Adapted sign helper for optional byte and flags, with cursor advancement bounded | Caller flag computation and full parser remain outside this mapping. |
| Options | Seventeen directly extracted release methods and STANDARD | Original build_strict hits an Aeneas internal error; parser behavior is outside this profile. |
| Options strict adapted | Strict constructor and SMALL_NUMBERS/LARGE_NUMBERS with a checked source replacement of the unreachable error-arm panic | Formal Rust-to-Rust equivalence remains open. |
| Generic checked | Complete-mode checked scalar adaptations for all integer widths and radices 2 through 36, with cursor and signed-entry premises | Front-end selection, partial mode and release equivalence remain outside these helper theorems. |
| Generic partial | Partial-mode checked scalar adaptations for all integer widths and radices 2 through 36, with cursor and signed-entry premises | Front-end selection and release equivalence remain outside these helper theorems. |
| Generic front | Complete and partial adapted front ends for every integer width and radix 2 through 36 on arbitrary bytes, with standard no-format syntax and no_multi_digit=true | usize/isize require a 64-bit platform. Safe iterator, outlined macro and front-end adaptations are source checked and reviewed; formal release equivalence and original raw-memory paths remain open. |

These adapted-body results do not close the original-release rows above. See
each profile's report for exact premises and mappings.

An extraction failure leaves the affected algorithm row open even if a helper
extracts or proves. Builder/accessor or arithmetic model lemmas close no public
parser row. Native tests, exhaustive finite checks, generated Lean compilation,
and formal proofs are reported separately. A source adaptation requires both a
recorded release diff and a separately stated equivalence obligation; neither
testing nor proof of the adapted code alone proves release equivalence.
