# Default decimal parser adaptation

The parser harness outlines the release's scalar digit macros. The source
checker compares all 15 selected loop bodies after explicit radix, accumulator,
error, iterator, and cursor substitutions. It also freezes 11 reviewed
complete and partial `u8`/`i8` front-end bodies. These checks establish the
disclosed textual relationship; they are separate from the Lean body proofs and
do not constitute a Rust-to-Rust equivalence theorem for the generic parser.

The release chooses one unchecked decimal digit for `i8` (`overflow_digits`
is one), then uses checked addition or subtraction on the rest. For negative
input with at most one digit, the release's first unchecked negative loop
consumes the iterator. Its later positive unchecked loop sees that same
exhausted iterator and makes no change. The adapted front end returns after
the negative loop. An invalid first digit already returns from the release
macro before that later loop; the adaptation preserves the corresponding
complete error or partial value and count. For longer input the harness uses
slices to express the one-digit prefix and remaining suffix with absolute
cursor offsets.

The release's `parse_sign!` mutates its byte iterator on an accepted sign. The
parser harness instead selects one optional leading sign and passes an
explicit offset. The `i8` model accepts `+` or `-`, while `u8` accepts `+`;
empty post-sign input produces `Empty` at that offset. Native release
correspondence tests check these adapters separately from formal proof. The
standalone sign profile covers all helper flag combinations, but caller flag
calculation and generic parser equivalence remain separate obligations.
