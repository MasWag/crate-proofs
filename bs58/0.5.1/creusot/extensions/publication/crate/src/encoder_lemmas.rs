//! Checked arithmetic and sequence bridges for the Base58 encoder.
use creusot_std::prelude::*;
use crate::{spec, lemmas};

#[logic(opaque)]
#[variant(input.len())]
#[ensures(result && (0 <= spec::leading(input, zero) && spec::leading(input, zero) <= input.len()))]
pub fn leading_bounds(input: Seq<u8>, zero: u8) -> bool {
    pearlite! { if input.len() == 0 || input[0] != zero {
        0 <= spec::leading(input, zero) && spec::leading(input, zero) <= input.len()
    } else { leading_bounds(input.subsequence(1, input.len()), zero)
        && 0 <= spec::leading(input, zero) && spec::leading(input, zero) <= input.len() } }
}

#[logic(opaque)]
#[requires(0 <= n && n <= input.len())]
#[requires(forall<k: Int> 0 <= k && k < n ==> input[k] == zero)]
#[variant(n)]
#[ensures(result && (n <= spec::leading(input, zero)))]
pub fn leading_lower(input: Seq<u8>, zero: u8, n: Int) -> bool {
    pearlite! { if n == 0 { leading_bounds(input, zero) && n <= spec::leading(input, zero) }
    else { leading_lower(input.subsequence(1, input.len()), zero, n - 1)
        && n <= spec::leading(input, zero) } }
}

#[logic(opaque)]
#[requires(radix >= 2)]
#[variant(input.len())]
#[ensures(result && (0 <= spec::le(input, radix)))]
pub fn le_nonnegative(input: Seq<u8>, radix: Int) -> bool {
    pearlite! { if input.len() == 0 { 0 <= spec::le(input, radix) }
    else { le_nonnegative(input.subsequence(1, input.len()), radix) && 0 <= spec::le(input, radix) } }
}

#[logic(opaque)]
#[requires(forall<k: Int> 0 <= k && k < input.len() ==> input[k] == 0u8)]
#[variant(input.len())]
#[ensures(result && (spec::le(input, radix) == 0))]
pub fn le_zero(input: Seq<u8>, radix: Int) -> bool {
    pearlite! { if input.len() == 0 { spec::le(input, radix) == 0 }
    else { le_zero(input.subsequence(1, input.len()), radix) && spec::le(input, radix) == 0 } }
}

#[logic(opaque)]
#[requires(0 <= n && n <= m && m <= input.len())]
#[requires(forall<k: Int> n <= k && k < m ==> input[k] == 0u8)]
#[ensures(result && (spec::le(input.subsequence(0, m), radix) == spec::le(input.subsequence(0, n), radix)))]
pub fn le_zero_suffix(input: Seq<u8>, radix: Int, n: Int, m: Int) -> bool {
    pearlite! { spec::le_split(input.subsequence(0, m), radix, n)
        && input.subsequence(0, m).subsequence(0, n) == input.subsequence(0, n)
        && input.subsequence(0, m).subsequence(n, m) == input.subsequence(n, m)
        && le_zero(input.subsequence(n, m), radix)
        && spec::le(input.subsequence(0, m), radix) == spec::le(input.subsequence(0, n), radix) }
}

#[logic(opaque)]
#[requires(0 <= n && n < before.len() && n < after.len())]
#[requires(forall<k: Int> 0 <= k && k < n ==> before[k] == after[k])]
#[ensures(result && (spec::le(after.subsequence(0, n + 1), radix)
    == spec::le(before.subsequence(0, n), radix) + spec::pow(radix, n) * after[n]@))]
pub fn le_extend(before: Seq<u8>, after: Seq<u8>, radix: Int, n: Int) -> bool {
    pearlite! { after.subsequence(0, n) == before.subsequence(0, n)
        && after.subsequence(0, n + 1).len() == n + 1
        && after.subsequence(0, n + 1).subsequence(0, n) == after.subsequence(0, n)
        && after.subsequence(0, n + 1).subsequence(0, n) == before.subsequence(0, n)
        && spec::le_split(after.subsequence(0, n + 1), radix, n)
        && after.subsequence(0, n + 1).subsequence(n, n + 1).len() == 1
        && after.subsequence(0, n + 1).subsequence(n, n + 1)[0] == after[n]
        && after.subsequence(0, n + 1).subsequence(n, n + 1).subsequence(1, 1).len() == 0
        && spec::le(after.subsequence(0, n + 1).subsequence(n, n + 1), radix) == after[n]@
        && spec::le(after.subsequence(0, n + 1).subsequence(n, after.subsequence(0, n + 1).len()), radix) == after[n]@
        && spec::le(after.subsequence(0, n + 1).subsequence(0, n), radix) == spec::le(before.subsequence(0, n), radix)
        && spec::le(after.subsequence(0, n + 1), radix)
            == spec::le(before.subsequence(0, n), radix) + spec::pow(radix, n) * after[n]@ }
}

#[logic(opaque)]
#[requires(radix >= 2 && 0 < n && n <= input.len())]
#[requires(input[n - 1] != 0u8)]
#[ensures(result && (spec::pow(radix, n - 1) <= spec::le(input.subsequence(0, n), radix)))]
pub fn le_canonical_lower(input: Seq<u8>, radix: Int, n: Int) -> bool {
    pearlite! { le_extend(input, input, radix, n - 1)
        && le_nonnegative(input.subsequence(0, n - 1), radix)
        && spec::pow_positive(radix, n - 1)
        && input[n - 1]@ >= 1
        && spec::pow(radix, n - 1) * input[n - 1]@ >= spec::pow(radix, n - 1)
        && spec::pow(radix, n - 1) <= spec::le(input.subsequence(0, n), radix) }
}

#[logic(opaque)]
#[requires(0 <= consumed && consumed <= input.len() && capacity == digits.len() && carry > 0)]
#[requires(forall<k: Int> 0 <= k && k < capacity ==> digits[k]@ < 58)]
#[requires(spec::le(digits.subsequence(0, capacity), 58) + spec::pow(58, capacity) * carry
    == spec::be(input.subsequence(0, consumed), 256))]
#[ensures(result && (!spec::encode_fits(input, capacity)))]
pub fn encode_growth_failure(input: Seq<u8>, digits: Seq<u8>, consumed: Int, capacity: Int, carry: Int) -> bool {
    pearlite! { leading_bounds(input, 0u8)
        && lemmas::le_bound(digits.subsequence(0, capacity), 58)
        && spec::pow_positive(58, capacity)
        && lemmas::be_prefix_monotone(input, 256, consumed, input.len())
        && input.subsequence(0, input.len()) == input
        && (if spec::leading(input, 0u8) <= capacity {
            lemmas::pow_monotone(58, capacity - spec::leading(input, 0u8), capacity)
                && !spec::encode_fits(input, capacity)
        } else { !spec::encode_fits(input, capacity) }) }
}

#[logic(opaque)]
#[requires(0 <= zeros && zeros < input.len() && 0 <= capacity && zeros <= capacity && capacity == digits.len())]
#[requires(forall<k: Int> 0 <= k && k <= zeros ==> input[k] == 0u8)]
#[requires(forall<k: Int> capacity - zeros <= k && k < capacity ==> digits[k] == 0u8)]
#[requires(capacity == zeros || digits[capacity - zeros - 1] != 0u8)]
#[requires(spec::le(digits.subsequence(0, capacity), 58) == spec::be(input, 256))]
#[ensures(result && (!spec::encode_fits(input, capacity)))]
pub fn encode_zero_failure(input: Seq<u8>, digits: Seq<u8>, zeros: Int, capacity: Int) -> bool {
    pearlite! { leading_lower(input, 0u8, zeros + 1)
        && le_zero_suffix(digits, 58, capacity - zeros, capacity)
        && (if spec::leading(input, 0u8) <= capacity {
            le_canonical_lower(digits, 58, capacity - zeros)
                && lemmas::pow_monotone(58, capacity - spec::leading(input, 0u8), capacity - zeros - 1)
                && !spec::encode_fits(input, capacity)
        } else { !spec::encode_fits(input, capacity) }) }
}

#[logic(opaque)]
#[requires(0 <= zeros && zeros <= n && n <= digits.len())]
#[requires(zeros == spec::leading(input, 0u8))]
#[requires(forall<k: Int> 0 <= k && k < n ==> digits[k]@ < 58)]
#[requires(forall<k: Int> n - zeros <= k && k < n ==> digits[k] == 0u8)]
#[requires(spec::le(digits.subsequence(0, n), 58) == spec::be(input, 256))]
#[ensures(result && (spec::encode_fits(input, digits.len())))]
pub fn encode_success_fits(input: Seq<u8>, digits: Seq<u8>, zeros: Int, n: Int) -> bool {
    pearlite! { le_zero_suffix(digits, 58, n - zeros, n)
        && lemmas::le_bound(digits.subsequence(0, n - zeros), 58)
        && lemmas::pow_monotone(58, n - zeros, digits.len() - zeros)
        && spec::encode_fits(input, digits.len()) }
}

/// Euclidean division preserves the weighted digit plus carry.
#[logic(opaque)]
#[ensures(result && (p * value == p * (value % 58) + (58 * p) * (value / 58)))]
pub fn division_weight(p: Int, value: Int) -> bool {
    pearlite! {
        value == value % 58 + 58 * (value / 58)
            && p * value == p * (value % 58) + (58 * p) * (value / 58)
    }
}

/// One Horner digit update, stated independently of Rust array mutation.
#[logic(opaque)]
#[ensures(result && (prefix + p * carry + 256 * p * (digit + 58 * tail)
    == prefix + p * ((carry + 256 * digit) % 58)
        + (58 * p) * ((carry + 256 * digit) / 58) + 256 * (58 * p) * tail))]
pub fn horner_weight(prefix: Int, p: Int, carry: Int, digit: Int, tail: Int) -> bool {
    pearlite! {
        division_weight(p, carry + 256 * digit)
            && prefix + p * carry + 256 * p * (digit + 58 * tail)
                == prefix + p * (carry + 256 * digit) + 256 * (58 * p) * tail
            && prefix + p * carry + 256 * p * (digit + 58 * tail)
                == prefix + p * ((carry + 256 * digit) % 58)
                    + (58 * p) * ((carry + 256 * digit) / 58) + 256 * (58 * p) * tail
    }
}

#[logic(opaque)]
#[requires(new_prefix == old_prefix + p * digit && q == 58 * p)]
#[requires(digit == carry % 58 && next_carry == carry / 58)]
#[ensures(result && (new_prefix + q * next_carry == old_prefix + p * carry))]
pub fn append_preserves(old_prefix: Int, p: Int, carry: Int,
    new_prefix: Int, q: Int, next_carry: Int, digit: Int) -> bool {
    pearlite! { division_weight(p, carry)
        && new_prefix + q * next_carry == old_prefix + p * carry }
}

#[logic(opaque)]
#[requires(old_tail == old_digit + 58 * new_tail)]
#[requires(new_prefix == old_prefix + p * new_digit && q == 58 * p)]
#[requires(new_digit == (carry + 256 * old_digit) % 58
    && next_carry == (carry + 256 * old_digit) / 58)]
#[ensures(result && (new_prefix + q * next_carry + 256 * q * new_tail
    == old_prefix + p * carry + 256 * p * old_tail))]
pub fn horner_preserves(old_prefix: Int, p: Int, carry: Int, old_digit: Int, old_tail: Int,
    new_prefix: Int, q: Int, next_carry: Int, new_digit: Int, new_tail: Int) -> bool {
    pearlite! { horner_weight(old_prefix, p, carry, old_digit, new_tail)
        && new_prefix + q * next_carry + 256 * q * new_tail
            == old_prefix + p * carry + 256 * p * old_tail }
}

/// Ghost-call form exposes the checked transition directly at the call site.
#[check(ghost)]
#[requires(*new_prefix == *old_prefix + *p * *digit && *q == 58 * *p)]
#[requires(*digit == *carry % 58 && *next_carry == *carry / 58)]
#[ensures(*new_prefix + *q * *next_carry == *old_prefix + *p * *carry)]
pub fn append_step(old_prefix: Snapshot<Int>, p: Snapshot<Int>, carry: Snapshot<Int>,
    new_prefix: Snapshot<Int>, q: Snapshot<Int>, next_carry: Snapshot<Int>, digit: Snapshot<Int>) {
    proof_assert!(append_preserves(*old_prefix, *p, *carry, *new_prefix, *q, *next_carry, *digit));
}

#[check(ghost)]
#[requires(*old_tail == *old_digit + 58 * *new_tail)]
#[requires(*new_prefix == *old_prefix + *p * *new_digit && *q == 58 * *p)]
#[requires(*new_digit == (*carry + 256 * *old_digit) % 58
    && *next_carry == (*carry + 256 * *old_digit) / 58)]
#[ensures(*new_prefix + *q * *next_carry + 256 * *q * *new_tail
    == *old_prefix + *p * *carry + 256 * *p * *old_tail)]
pub fn horner_step(old_prefix: Snapshot<Int>, p: Snapshot<Int>, carry: Snapshot<Int>,
    old_digit: Snapshot<Int>, old_tail: Snapshot<Int>, new_prefix: Snapshot<Int>,
    q: Snapshot<Int>, next_carry: Snapshot<Int>, new_digit: Snapshot<Int>, new_tail: Snapshot<Int>) {
    proof_assert!(horner_preserves(*old_prefix, *p, *carry, *old_digit, *old_tail,
        *new_prefix, *q, *next_carry, *new_digit, *new_tail));
}
