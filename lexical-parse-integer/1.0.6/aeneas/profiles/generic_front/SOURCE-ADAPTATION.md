# Generic scalar frontend adaptation

The selected release is `lexical-parse-integer` 1.0.6 with `lexical-util` 1.0.7. The proof target is the separately extracted `verification/generic-parser-front-harness`, with `no_multi_digit=true`, the standard sign syntax, and radix 2 through 36. It instantiates complete and partial parsing for `u8/u16/u32/u64/u128/usize` and `i8/i16/i32/i64/i128/isize`. The whole-input contracts come from Astra's `GenericScalarSpecs.lean` and quantify over every byte slice; `usize` and `isize` whole-input theorems explicitly assume the selected 64-bit platform width.

The safe adaptation replaces `Bytes`/`DigitsIter` and raw cursor observations with a slice plus absolute `usize` cursor. The source checker compares the release's `parse_1digit_unchecked!` token sequence against all four instantiated unchecked loop macro families after this substitution. It also checks the release's `parse_digits_checked!` order: `take_n(overflow_digits)`, unchecked scalar prefix, then checked scalar continuation. The checked continuations are separate extracted `generic_checked` and `generic_partial` bodies. Complete invalid digits return `InvalidDigit(cursor-1)`; partial invalid digits return the value and unconsumed-byte cursor. The source checker compares the frontend sign, empty, prefix-cutoff, early partial return, checked continuation, and all 24 width/type macro invocations against reviewed templates. `overflow_digits` is compared with the locked `lexical-util::num::Integer` method after replacing `size_of::<Self>()` and `IS_SIGNED` with explicit byte width and sign parameters.

For a short negative input, the release runs the unchecked negative loop and
then enters an unchecked positive loop. The adapter returns directly after the
negative loop because it has consumed the entire remaining suffix. If that loop
encounters an invalid byte, the original negative macro already returns early,
so the positive loop is not a continuation of that case either. This is source
reasoning about the adaptation, not a formal equivalence proof.

The checker validates all selected `lexical-util` source files against the locked archive, checks that the independently authored `DigitSpecs.lean` and `GenericScalarSpecs.lean` are byte-identical copies, and confirms the helper source adaptation separately. It is a source correspondence check, not a formal equivalence theorem between the original release iterator/raw memory and the safe adapter. The whole-input proofs establish behavior of the extracted adapted Rust bodies. Format-specific separators, prefixes and suffixes, the multi-digit fast path, and option-independence are outside this profile.
