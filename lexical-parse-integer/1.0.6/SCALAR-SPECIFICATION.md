# Scoped scalar and caller contracts

This extends [SPECIFICATION.md](SPECIFICATION.md); it does not replace its full
parser obligations or claim any additional proof is complete. The scoped scalar
work covers standalone decimal checked-loop outlines for `u32` and both signs
of `i32`, and a separate decimal complete-parser adaptation for `u8`. Loop
contracts do not establish the wider parser's front end or fast paths. The `u8`
front end avoids the four/eight-digit fast paths by its width; `i8` remains a
further front-end obligation. Extend to other widths and supported radices only
with explicit instantiations or a proved parametric contract. Inputs remain arbitrary
bytes, including empty input, signs, nondigits and overlong digit sequences.
Do not restrict the public contract to successful inputs.

## Independent scanning relation

Use the independent `digit_r`, digit fold and representation bounds from the
main specification. A scan state consists of original byte list `xs`, cursor
`j <= xs.length`, magnitude `P`, radix `r`, sign `negative`, and target bound
`B`. Its represented mathematical value is `P` or `-P`. Before scanning,
require `P <= B`; for a signed machine accumulator require the corresponding
sign discipline, not merely membership in the signed representation interval.

For the maximal digit run from `j`, define the sequence of magnitudes by
`P[0]=P` and `P[k+1]=r*P[k]+digit(xs[j+k])`. The scan stops at the first of:

* A digit at original index `j+k` for which `P[k+1]>B`: return
  `Overflow(j+k)` for nonnegative accumulation or `Underflow(j+k)` for
  negative accumulation. Earlier digits have in-range magnitudes.
* A nondigit at original index `j+k`: complete mode returns
  `InvalidDigit(j+k)`; partial mode returns the signed value of `P[k]` and
  consumed length `j+k`. The nondigit is not part of the consumed prefix.
* The end of input: return the signed value of the final magnitude; partial
  mode additionally returns `xs.length`.

Earlier events take precedence. For example, overflow before a later nondigit
remains overflow; a nondigit is never treated as a digit that caused overflow.
The recursive relation decreases the remaining input length, independently of
the release's loop representation. A proof must relate the actual extracted
loop to this relation and prove total Aeneas success, including normal Rust
error results.

## Small independent proof units

| Unit | Required guarantee |
| --- | --- |
| Byte-to-digit conversion | For every byte and supported `2<=r<=36`, return exactly `digit_r`; no ASCII/validity premise. |
| Checked unsigned step | For `P<=2^w-1` and `d<r`, return `Some(r*P+d)` exactly when it fits; otherwise `None`. |
| Checked signed positive step | Same with `0<=v=P<=2^(w-1)-1`, addition and positive bound. |
| Checked signed negative step | With `v=-P<=0`, return `Some(-(r*P+d))` exactly when magnitude is at most `2^(w-1)`; otherwise `None`. |
| Checked scan | Exact relation above, including first error position and partial consumed length, for all remaining bytes. |
| Unchecked scan | Same value/cursor relation on a region whose magnitude bound is proved from its entry state and length. |
| Parser front end | Sign handling and empty-input result feed the exact original cursor and zero accumulator into the scan relation. |

The sign premises on private signed-step lemmas are essential: checked
multiplication can overflow before an opposite-sign addition brings the final
mathematical result back into range. The release uses addition only on its
nonnegative path and subtraction only on its nonpositive path; public proofs
must establish that invariant. No assumption about the implementation's returned
result is permitted.

For an unchecked region of at most `k` digits entered with magnitude `P`, a
sufficient independent bound is `r^k*P+(r^k-1)<=B`. At the parser's initial
zero accumulator this reduces to `r^k-1<=B`. Invalid bytes terminate before
being included in that bound. The actual `Integer::overflow_digits` choice
must satisfy it: for byte width `s`, the release chooses `2*s-signed` when
`r<=16`, and `s` otherwise. This is a private optimization obligation, not
a new length restriction on public parsing. For negative signed accumulation,
the positive bound is a sufficient conservative bound; the checked remainder
must still accept the exact signed minimum.

## Sign and empty-input front end

At initial cursor zero, standard syntax consumes an optional `+`, or an
optional `-` only for signed target types. The sign contributes to all later
byte positions. Empty input and input consisting only of an accepted sign
return `Empty(s)` where `s` is the post-sign cursor. An unsigned `-` is not
consumed as a sign. A second sign is a nondigit. The standard partial-parser
zero-digit behavior documented in the main specification remains explicit:
nonempty post-sign nondigit input may return zero with consumed count `s`.

A separate sign-helper contract may cover custom sign flags without claiming
the full custom grammar: forbidden `+` returns `InvalidPositiveSign(j)`;
accepted `+` advances once and selects nonnegative accumulation; accepted
signed `-` advances once and selects negative accumulation; otherwise a
required sign returns `MissingSign(j)`, including end of input; absent an
obligation the cursor remains unchanged and accumulation is nonnegative.
The helper does not itself reject sign-only input: that belongs to the parser.

## Iterator and block-caller boundaries

The `lexical-util` 1.0.7 no-skip iterator's `next` returns the byte at its old
cursor and increments once, including for a nondigit. Thus a scan's exposed
error/partial position is the returned byte's original index, not the internal
post-read cursor. `current_count` equals the absolute cursor for this iterator;
it is not an independently tracked count of numeric digits.

Its `take_n(k)` sets the outer cursor to `min(length, old_cursor+k)` and returns
an iterator over the original prefix slice with the old cursor. Therefore the
inner iterator retains absolute positions. On an early parser return, outer
and inner cursor equality is not an invariant. Prove the actual cursor addition
is representable or use the release's real slice/target bounds to discharge it;
do not silently model `usize` addition as unbounded arithmetic.

For `try_parse_4digits`/`try_parse_8digits`, the complete caller contract is:
insufficient bytes or a nondigit in the next block returns `None` without
advancing; a valid block returns its positional value (subject to the actual
target cast semantics) and advances exactly four/eight original bytes. A
numeric-value theorem needs a target bound ensuring the cast preserves that
value; the parser's selected target widths discharge it. The raw unaligned
read and `from_le` must be related to those next bytes in textual order.
Proving a convenient array replacement does not establish that memory bridge.

Appending a proved block of `k` digits with value `D` updates magnitude to
`r^k*P+D`, and its cursor advances by `k`. The outer unchecked region's bound
must show this equals the intended mathematical value without wrapping. This
is the connection still needed between standalone packed-word helpers and
whole-parser correctness.

## Source correspondence and remaining grammar

Preferred proofs use actual release functions or a faithful outlining of their
macros/loops. Record each substitution, specialization, control-flow rewrite,
and iterator/memory adaptation. Prove the new generated body and track its
equivalence to the release separately; a mathematically correct replacement
parser is not by itself evidence about this crate. An option-specific source
trial must state its option domain and cannot establish options equivalence.

Custom prefixes, suffixes, separators, leading-zero policy and optional digits
remain the explicit grammar obligations in the main specification. The two
retained custom-format cursor defects must not be hidden by weakening the
intended consumed-prefix or invalid-byte position contracts.
