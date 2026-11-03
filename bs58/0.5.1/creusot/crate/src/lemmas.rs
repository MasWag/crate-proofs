//! Checked radix lemmas used by the codec loop proofs.
use creusot_std::prelude::*;
use crate::spec::{be, be58, be58_step, be_step, digit, good_prefix, le, leading, pow, pow_positive, valid_alphabet};
use crate::{encoder_lemmas, spec};

/// Expose one little-endian digit from a bounded prefix without carrying the
/// recursive split hypothesis into the sequence normalization proof.
#[logic(opaque)]
#[requires(0 < n && n <= input.len())]
#[ensures(result && le(input.subsequence(0, n), radix)
    == input[0]@ + radix * le(input.subsequence(1, input.len())
        .subsequence(0, n - 1), radix))]
pub fn le_prefix_head(input: Seq<u8>, radix: Int, n: Int) -> bool {
    pearlite! {
        input.subsequence(0, n).len() == n
            && input.subsequence(0, n)[0] == input[0]
            && input.subsequence(0, n).subsequence(1, n)
                == input.subsequence(1, input.len()).subsequence(0, n - 1)
            && le(input.subsequence(0, n), radix)
                == input.subsequence(0, n)[0]@ + radix
                    * le(input.subsequence(0, n).subsequence(1, n), radix)
            && le(input.subsequence(0, n), radix)
                == input[0]@ + radix * le(input.subsequence(1, input.len())
                    .subsequence(0, n - 1), radix)
    }
}

/// The arithmetic part of the recursive split step, isolated from sequence
/// unfolding and quantifier instantiation.
#[logic(opaque)]
#[requires(whole == head + radix * tail)]
#[requires(tail == prefix_tail + prev_power * suffix)]
#[requires(prefix == head + radix * prefix_tail)]
#[requires(power == radix * prev_power)]
#[ensures(result && whole == prefix + power * suffix)]
pub fn le_split_algebra(whole: Int, prefix: Int, tail: Int, prefix_tail: Int,
    suffix: Int, head: Int, radix: Int, prev_power: Int, power: Int) -> bool {
    pearlite! { whole == prefix + power * suffix }
}

/// Division by 256 preserves a weighted integer, independently of array
/// indexing and the recursive digit-value definitions.
#[logic(opaque)]
#[requires(value >= 0)]
#[ensures(result && p * value == p * (value % 256) + (256 * p) * (value / 256))]
pub fn decode_division_weight(p: Int, value: Int) -> bool {
    pearlite! {
        value == value % 256 + 256 * (value / 256)
            && p * value == p * (value % 256) + (256 * p) * (value / 256)
    }
}

/// The Base58 digit's contribution becomes a base-256 quotient and remainder.
#[logic(opaque)]
#[requires(carry >= 0 && digit >= 0)]
#[ensures(result && prefix + p * carry + 58 * p * (digit + 256 * tail)
    == prefix + p * ((carry + 58 * digit) % 256)
        + (256 * p) * ((carry + 58 * digit) / 256) + 58 * (256 * p) * tail)]
pub fn decode_horner_weight(prefix: Int, p: Int, carry: Int, digit: Int, tail: Int) -> bool {
    pearlite! {
        decode_division_weight(p, carry + 58 * digit)
            && prefix + p * carry + 58 * p * (digit + 256 * tail)
                == prefix + p * (carry + 58 * digit) + 58 * (256 * p) * tail
            && prefix + p * carry + 58 * p * (digit + 256 * tail)
                == prefix + p * ((carry + 58 * digit) % 256)
                    + (256 * p) * ((carry + 58 * digit) / 256)
                    + 58 * (256 * p) * tail
    }
}

/// Algebraic decoder carry step. The caller supplies the separately proved
/// LE prefix-extension and suffix-split equalities as integer arguments.
#[logic(opaque)]
#[requires(carry >= 0 && old_digit >= 0)]
#[requires(old_tail == old_digit + 256 * new_tail)]
#[requires(new_prefix == old_prefix + p * new_digit && q == 256 * p)]
#[requires(new_digit == (carry + 58 * old_digit) % 256
    && next_carry == (carry + 58 * old_digit) / 256)]
#[ensures(result && new_prefix + q * next_carry + 58 * q * new_tail
    == old_prefix + p * carry + 58 * p * old_tail)]
pub fn decode_carry_step(old_prefix: Int, p: Int, carry: Int, old_digit: Int,
    old_tail: Int, new_prefix: Int, q: Int, next_carry: Int,
    new_digit: Int, new_tail: Int) -> bool {
    pearlite! {
        decode_horner_weight(old_prefix, p, carry, old_digit, new_tail)
            && new_prefix + q * next_carry + 58 * q * new_tail
                == old_prefix + p * carry + 58 * p * old_tail
    }
}

#[logic(opaque)]
#[requires(carry >= 0)]
#[requires(new_prefix == old_prefix + p * digit && q == 256 * p)]
#[requires(digit == carry % 256 && next_carry == carry / 256)]
#[ensures(result && new_prefix + q * next_carry == old_prefix + p * carry)]
pub fn decode_append_preserves(old_prefix: Int, p: Int, carry: Int,
    new_prefix: Int, q: Int, next_carry: Int, digit: Int) -> bool {
    pearlite! {
        decode_division_weight(p, carry)
            && new_prefix + q * next_carry == old_prefix + p * carry
    }
}

/// Ghost-call form of the checked decoder carry update.
#[check(ghost)]
#[requires(*carry >= 0 && *old_digit >= 0)]
#[requires(*old_tail == *old_digit + 256 * *new_tail)]
#[requires(*new_prefix == *old_prefix + *p * *new_digit && *q == 256 * *p)]
#[requires(*new_digit == (*carry + 58 * *old_digit) % 256
    && *next_carry == (*carry + 58 * *old_digit) / 256)]
#[ensures(*new_prefix + *q * *next_carry + 58 * *q * *new_tail
    == *old_prefix + *p * *carry + 58 * *p * *old_tail)]
pub fn decode_horner_step(old_prefix: Snapshot<Int>, p: Snapshot<Int>, carry: Snapshot<Int>,
    old_digit: Snapshot<Int>, old_tail: Snapshot<Int>, new_prefix: Snapshot<Int>,
    q: Snapshot<Int>, next_carry: Snapshot<Int>, new_digit: Snapshot<Int>,
    new_tail: Snapshot<Int>) {
    proof_assert!(decode_carry_step(*old_prefix, *p, *carry, *old_digit, *old_tail,
        *new_prefix, *q, *next_carry, *new_digit, *new_tail));
}

/// Ghost-call form of the checked decoder append update.
#[check(ghost)]
#[requires(*carry >= 0)]
#[requires(*new_prefix == *old_prefix + *p * *digit && *q == 256 * *p)]
#[requires(*digit == *carry % 256 && *next_carry == *carry / 256)]
#[ensures(*new_prefix + *q * *next_carry == *old_prefix + *p * *carry)]
pub fn decode_append_step(old_prefix: Snapshot<Int>, p: Snapshot<Int>, carry: Snapshot<Int>,
    new_prefix: Snapshot<Int>, q: Snapshot<Int>, next_carry: Snapshot<Int>,
    digit: Snapshot<Int>) {
    proof_assert!(decode_append_preserves(*old_prefix, *p, *carry,
        *new_prefix, *q, *next_carry, *digit));
}

/// Carry prefix extension to the caller's exact next-index expression.
#[check(ghost)]
#[requires(0 <= *n && *n < (*before).len() && *n < (*after).len())]
#[requires(*next == *n + 1)]
#[requires(forall<k: Int> 0 <= k && k < *n ==> (*before)[k] == (*after)[k])]
#[ensures(le((*after).subsequence(0, *next), *radix)
    == le((*before).subsequence(0, *n), *radix) + pow(*radix, *n) * (*after)[*n]@)]
pub fn le_extend_step(before: Snapshot<Seq<u8>>, after: Snapshot<Seq<u8>>,
    radix: Snapshot<Int>, n: Snapshot<Int>, next: Snapshot<Int>) {
    proof_assert!(encoder_lemmas::le_extend(*before, *after, *radix, *n));
}

/// Expose an unchanged decoder suffix using the caller's exact next index.
#[check(ghost)]
#[requires(0 <= *pos && *pos < *end
    && *end <= (*before).len() && *end <= (*after).len())]
#[requires(*next == *pos + 1)]
#[requires((*before).subsequence(*next, *end) == (*after).subsequence(*next, *end))]
#[ensures(le((*before).subsequence(*pos, *end), 256)
    == (*before)[*pos]@ + 256 * le((*after).subsequence(*next, *end), 256))]
pub fn decode_tail_step(before: Snapshot<Seq<u8>>, after: Snapshot<Seq<u8>>,
    pos: Snapshot<Int>, next: Snapshot<Int>, end: Snapshot<Int>) {
    proof_assert!((*before).subsequence(*pos, *end).subsequence(1, *end - *pos)
        == (*before).subsequence(*next, *end));
    proof_assert!(le((*before).subsequence(*pos, *end), 256)
        == (*before)[*pos]@ + 256 * le((*after).subsequence(*next, *end), 256));
}

/// Normalize a full occupied prefix before passing its value to a caller.
#[check(ghost)]
#[requires(*n == (*seq).len())]
#[ensures(le((*seq).subsequence(0, *n), 256) == le(*seq, 256))]
pub fn full_prefix_le(seq: Snapshot<Seq<u8>>, n: Snapshot<Int>) {
    proof_assert!((*seq).subsequence(0, *n) == *seq);
}

#[logic(opaque)]
#[requires(radix >= 2 && n >= 0)]
#[ensures(result && pow(radix, n) <= pow(radix, n + 1))]
pub fn pow_growth(radix: Int, n: Int) -> bool {
    pearlite! {
        pow_positive(radix, n)
            && pow(radix, n) <= pow(radix, n + 1)
    }
}

#[logic(opaque)]
#[requires(radix >= 2 && 0 <= n && n <= m)]
#[variant(m - n)]
#[ensures(result && pow(radix, n) <= pow(radix, m))]
pub fn pow_monotone(radix: Int, n: Int, m: Int) -> bool {
    pearlite! {
        if n == m { pow(radix, n) <= pow(radix, m) }
        else {
            pow_growth(radix, n)
                && pow_monotone(radix, n + 1, m)
                && pow(radix, n) <= pow(radix, m)
        }
    }
}

/// Every bounded little-endian digit sequence denotes an integer in the
/// corresponding radix interval. The nonnegative bound is useful in the
/// Horner and capacity proofs.
#[logic(opaque)]
#[requires(radix >= 2)]
#[requires(forall<i: Int> 0 <= i && i < input.len() ==> input[i]@ < radix)]
#[variant(input.len())]
#[ensures(result && 0 <= le(input, radix) && le(input, radix) < pow(radix, input.len()))]
pub fn le_bound(input: Seq<u8>, radix: Int) -> bool {
    pearlite! {
        if input.len() == 0 {
            0 <= le(input, radix) && le(input, radix) < pow(radix, input.len())
        } else {
            le_bound(input.subsequence(1, input.len()), radix)
                && 0 <= le(input, radix)
                && le(input, radix) < pow(radix, input.len())
        }
    }
}

#[logic(opaque)]
#[requires(radix >= 2)]
#[requires(forall<i: Int> 0 <= i && i < input.len() ==> input[i]@ < radix)]
#[variant(input.len())]
#[ensures(result && 0 <= be(input, radix) && be(input, radix) < pow(radix, input.len()))]
pub fn be_bound(input: Seq<u8>, radix: Int) -> bool {
    pearlite! {
        if input.len() == 0 {
            0 <= be(input, radix) && be(input, radix) < pow(radix, input.len())
        } else {
            be_bound(input.subsequence(0, input.len() - 1), radix)
                && 0 <= be(input, radix)
                && be(input, radix) < pow(radix, input.len())
        }
    }
}

#[logic(opaque)]
#[requires(radix >= 2 && 0 <= n && n <= m && m <= input.len())]
#[requires(forall<i: Int> 0 <= i && i < m ==> input[i]@ < radix)]
#[variant(m - n)]
#[ensures(result && be(input.subsequence(0, n), radix)
    <= be(input.subsequence(0, m), radix))]
pub fn be_prefix_monotone(input: Seq<u8>, radix: Int, n: Int, m: Int) -> bool {
    pearlite! {
        if n == m {
            be(input.subsequence(0, n), radix)
                <= be(input.subsequence(0, m), radix)
        } else {
            be_bound(input.subsequence(0, n), radix)
                && be_step(input, radix, n)
                && be_prefix_monotone(input, radix, n + 1, m)
                && be(input.subsequence(0, n), radix)
                    <= radix * be(input.subsequence(0, n), radix)
                && radix * be(input.subsequence(0, n), radix)
                    <= radix * be(input.subsequence(0, n), radix) + input[n]@
                && be(input.subsequence(0, n), radix)
                    <= be(input.subsequence(0, n + 1), radix)
                && be(input.subsequence(0, n), radix)
                    <= be(input.subsequence(0, m), radix)
        }
    }
}

#[logic(opaque)]
#[requires(0 <= n && n <= m && m <= input.len())]
#[requires(good_prefix(input, decode, m))]
#[variant(m - n)]
#[ensures(result && be58(input.subsequence(0, n), decode)
    <= be58(input.subsequence(0, m), decode))]
pub fn be58_prefix_monotone(input: Seq<u8>, decode: Seq<u8>, n: Int, m: Int) -> bool {
    pearlite! {
        if n == m {
            be58(input.subsequence(0, n), decode)
                <= be58(input.subsequence(0, m), decode)
        } else {
            be58_nonnegative(input.subsequence(0, n), decode)
                && be58_step(input, decode, n)
                && be58_prefix_monotone(input, decode, n + 1, m)
                && be58(input.subsequence(0, n), decode)
                    <= be58(input.subsequence(0, m), decode)
        }
    }
}

#[logic(opaque)]
#[requires(good_prefix(input, decode, input.len()))]
#[variant(input.len())]
#[ensures(result && 0 <= be58(input, decode) && be58(input, decode) < pow(58, input.len()))]
pub fn be58_nonnegative(input: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! {
        if input.len() == 0 {
            0 <= be58(input, decode) && be58(input, decode) < pow(58, input.len())
        } else {
            be58_nonnegative(input.subsequence(0, input.len() - 1), decode)
                && 0 <= be58(input, decode)
                && be58(input, decode) < pow(58, input.len())
        }
    }
}

/// A pointwise reversal has the same integer value when read in the opposite
/// byte order. Both slices are exactly the occupied output prefix.
#[logic(opaque)]
#[requires(0 <= n && n <= little.len() && n <= big.len())]
#[requires(forall<k: Int> 0 <= k && k < n ==> little[k] == big[n - 1 - k])]
#[variant(n)]
#[ensures(result && le(little.subsequence(0, n), radix) == be(big.subsequence(0, n), radix))]
pub fn le_reverse_be(little: Seq<u8>, big: Seq<u8>, radix: Int, n: Int) -> bool {
    pearlite! {
        if n == 0 {
            le(little.subsequence(0, n), radix) == be(big.subsequence(0, n), radix)
        } else {
            le_reverse_be(little.subsequence(1, n), big.subsequence(0, n - 1), radix, n - 1)
                && little.subsequence(0, n).subsequence(1, n)
                    == little.subsequence(1, n)
                && big.subsequence(0, n).subsequence(0, n - 1)
                    == big.subsequence(0, n - 1)
                && little.subsequence(1, n).subsequence(0, n - 1)
                    == little.subsequence(1, n)
                && big.subsequence(0, n - 1).subsequence(0, n - 1)
                    == big.subsequence(0, n - 1)
                && le(little.subsequence(0, n), radix) == be(big.subsequence(0, n), radix)
        }
    }
}

/// The same reversal relation after replacing each Base58 digit with its
/// alphabet character. The caller supplies the exact decoded digit relation.
#[logic(opaque)]
#[requires(0 <= n && n <= little.len() && n <= big.len())]
#[requires(forall<k: Int> 0 <= k && k < n ==>
    little[k]@ == digit(decode, big[n - 1 - k]))]
#[variant(n)]
#[ensures(result && le(little.subsequence(0, n), 58) == be58(big.subsequence(0, n), decode))]
pub fn le_reverse_be58(little: Seq<u8>, big: Seq<u8>, decode: Seq<u8>, n: Int) -> bool {
    pearlite! {
        if n == 0 {
            le(little.subsequence(0, n), 58) == be58(big.subsequence(0, n), decode)
        } else {
            le_reverse_be58(little.subsequence(1, n), big.subsequence(0, n - 1), decode, n - 1)
                && little.subsequence(0, n).subsequence(1, n)
                    == little.subsequence(1, n)
                && big.subsequence(0, n).subsequence(0, n - 1)
                    == big.subsequence(0, n - 1)
                && little.subsequence(1, n).subsequence(0, n - 1)
                    == little.subsequence(1, n)
                && big.subsequence(0, n - 1).subsequence(0, n - 1)
                    == big.subsequence(0, n - 1)
                && le(little.subsequence(0, n), 58) == be58(big.subsequence(0, n), decode)
        }
    }
}

/// Connect the two pointwise observations made in the encoder: mapping through
/// the alphabet and then reversing. Alphabet validity supplies inverse lookup.
#[logic(opaque)]
#[requires(valid_alphabet(encode, decode))]
#[requires(0 <= n && n <= digits.len() && n <= mapped.len() && n <= output.len())]
#[requires(forall<k: Int> 0 <= k && k < n ==> digits[k]@ < 58)]
#[requires(forall<k: Int> 0 <= k && k < n ==> mapped[k] == encode[digits[k]@])]
#[requires(forall<k: Int> 0 <= k && k < n ==> output[k] == mapped[n - 1 - k])]
#[ensures(result && le(digits.subsequence(0, n), 58)
    == be58(output.subsequence(0, n), decode))]
pub fn alphabet_reverse_value(digits: Seq<u8>, mapped: Seq<u8>, output: Seq<u8>,
    encode: Seq<u8>, decode: Seq<u8>, n: Int) -> bool {
    pearlite! {
        le_reverse_be58(digits, output, decode, n)
            && le(digits.subsequence(0, n), 58)
                == be58(output.subsequence(0, n), decode)
    }
}

/// The exact zero-run length follows from the occupied prefix and the first
/// nonzero element, including an all-zero or empty prefix.
#[logic(opaque)]
#[requires(0 <= zeros && zeros <= n && n <= input.len())]
#[requires(forall<k: Int> 0 <= k && k < zeros ==> input[k] == zero)]
#[requires(zeros == n || input[zeros] != zero)]
#[variant(zeros)]
#[ensures(result && leading(input.subsequence(0, n), zero) == zeros)]
pub fn leading_exact(input: Seq<u8>, zero: u8, zeros: Int, n: Int) -> bool {
    pearlite! {
        if zeros == 0 {
            leading(input.subsequence(0, n), zero) == zeros
        } else {
            leading_exact(input.subsequence(1, n), zero, zeros - 1, n - 1)
                && input.subsequence(0, n)[0] == input[0]
                && input.subsequence(0, n).subsequence(1, n)
                    == input.subsequence(1, n)
                && input.subsequence(1, n).subsequence(0, n - 1)
                    == input.subsequence(1, n)
                && leading(input.subsequence(0, n), zero) == zeros
        }
    }
}

/// Turn a zero suffix of little-endian digits into the corresponding zero
/// prefix after reversal. Callers use this for both raw bytes and mapped
/// alphabet characters.
#[logic(opaque)]
#[requires(0 <= zeros && zeros <= n && n <= little.len() && n <= big.len())]
#[requires(forall<k: Int> 0 <= k && k < n ==> big[k] == little[n - 1 - k])]
#[requires(forall<k: Int> n - zeros <= k && k < n ==> little[k] == zero)]
#[requires(zeros == n || little[n - zeros - 1] != zero)]
#[ensures(result && leading(big.subsequence(0, n), zero) == zeros)]
pub fn leading_reverse(little: Seq<u8>, big: Seq<u8>, zero: u8, zeros: Int, n: Int) -> bool {
    pearlite! {
        leading_exact(big, zero, zeros, n)
            && leading(big.subsequence(0, n), zero) == zeros
    }
}

/// A completed decoder value occupies no more than the available byte slots,
/// including the leading zero bytes appended after magnitude conversion.
#[logic(opaque)]
#[requires(valid_alphabet(encode, decode) && good_prefix(input, decode, input.len()))]
#[requires(0 <= zeros && zeros <= n && n <= capacity && capacity == digits.len())]
#[requires(zeros == leading(input, encode[0]))]
#[requires(forall<k: Int> n - zeros <= k && k < n ==> digits[k] == 0u8)]
#[requires(le(digits.subsequence(0, n), 256) == be58(input, decode))]
#[ensures(result && spec::decode_fits(input, encode, decode, capacity))]
pub fn decode_success_fits(input: Seq<u8>, digits: Seq<u8>, encode: Seq<u8>,
    decode: Seq<u8>, zeros: Int, n: Int, capacity: Int) -> bool {
    pearlite! {
        encoder_lemmas::le_zero_suffix(digits, 256, n - zeros, n)
            && le_bound(digits.subsequence(0, n - zeros), 256)
            && pow_monotone(256, n - zeros, capacity - zeros)
            && spec::decode_fits(input, encode, decode, capacity)
    }
}

/// When another carry digit is needed at full capacity, the magnitude is at
/// least the first number requiring capacity + 1 bytes.
#[logic(opaque)]
#[requires(0 <= consumed && consumed <= input.len() && capacity == digits.len() && carry > 0)]
#[requires(good_prefix(input, decode, consumed))]
#[requires(le(digits, 256) + pow(256, capacity) * carry
    == be58(input.subsequence(0, consumed), decode))]
#[ensures(result && be58(input.subsequence(0, consumed), decode) >= pow(256, capacity))]
pub fn decode_growth_failure(input: Seq<u8>, digits: Seq<u8>, decode: Seq<u8>,
    consumed: Int, capacity: Int, carry: Int) -> bool {
    pearlite! {
        encoder_lemmas::le_nonnegative(digits, 256)
            && pow_positive(256, capacity)
            && be58(input.subsequence(0, consumed), decode) >= pow(256, capacity)
    }
}

/// If the zero run requires one more slot after capacity is full, either it
/// exceeds capacity outright or the canonical magnitude already needs all
/// remaining slots.
#[logic(opaque)]
#[requires(valid_alphabet(encode, decode) && good_prefix(input, decode, input.len()))]
#[requires(0 <= zeros && zeros < input.len() && zeros <= capacity && capacity == digits.len())]
#[requires(forall<k: Int> 0 <= k && k <= zeros ==> input[k] == encode[0])]
#[requires(forall<k: Int> capacity - zeros <= k && k < capacity ==> digits[k] == 0u8)]
#[requires(capacity == zeros || digits[capacity - zeros - 1] != 0u8)]
#[requires(le(digits, 256) == be58(input, decode))]
#[ensures(result && !spec::decode_fits(input, encode, decode, capacity))]
pub fn decode_zero_failure(input: Seq<u8>, digits: Seq<u8>, encode: Seq<u8>,
    decode: Seq<u8>, zeros: Int, capacity: Int) -> bool {
    pearlite! {
        encoder_lemmas::leading_lower(input, encode[0], zeros + 1)
            && encoder_lemmas::le_zero_suffix(digits, 256, capacity - zeros, capacity)
            && digits.subsequence(0, capacity) == digits
            && (if leading(input, encode[0]) <= capacity {
                encoder_lemmas::le_canonical_lower(digits, 256, capacity - zeros)
                    && pow_monotone(256, capacity - leading(input, encode[0]),
                        capacity - zeros - 1)
                    && be58(input, decode)
                        >= pow(256, capacity - leading(input, encode[0]))
                    && !spec::decode_fits(input, encode, decode, capacity)
            } else {
                !spec::decode_fits(input, encode, decode, capacity)
            })
    }
}

/// A positive canonical magnitude stays at least as wide when multiplied by
/// 58 and incremented. In the decoder this applies when conversion consumed
/// no additional byte slot; its highest occupied byte must stay nonzero.
#[logic(opaque)]
#[requires(0 < n && n <= old.len() && n <= new.len())]
#[requires(old[n - 1] != 0u8 && digit_value >= 0)]
#[requires(le(new.subsequence(0, n), 256)
    == 58 * le(old.subsequence(0, n), 256) + digit_value)]
#[ensures(result && new[n - 1] != 0u8)]
pub fn decode_canonical_growth(old: Seq<u8>, new: Seq<u8>, n: Int,
    digit_value: Int) -> bool {
    pearlite! {
        encoder_lemmas::le_canonical_lower(old, 256, n)
            && pow_positive(256, n - 1)
            && le(new.subsequence(0, n), 256) >= pow(256, n - 1)
            && (if new[n - 1] == 0u8 {
                encoder_lemmas::le_zero_suffix(new, 256, n - 1, n)
                    && le_bound(new.subsequence(0, n - 1), 256)
                    && le(new.subsequence(0, n), 256)
                        < pow(256, n - 1)
                    && false
            } else { new[n - 1] != 0u8 })
    }
}
