//! Independent mathematical specifications for the bs58 0.5.1 byte cores.
//! Definitions are not proof assumptions. All helper obligations must be proved.
use creusot_std::prelude::*;
use crate::{Alphabet, AlphabetError, DecodeError, EncodeError};

/// Integer powers; extending nonpositive exponents to 1 makes this total.
/// All codec specifications use nonnegative exponents and radix >= 2.
#[logic(open)]
#[variant(if n > 0 { n } else { 0 })]
pub fn pow(radix: Int, n: Int) -> Int {
    pearlite! { if n <= 0 { 1 } else { radix * pow(radix, n - 1) } }
}

/// Big-endian radix evaluation, independently of the conversion algorithm.
#[logic(open)]
#[variant(input.len())]
pub fn be(input: Seq<u8>, radix: Int) -> Int {
    pearlite! {
        if input.len() == 0 { 0 }
        else { radix * be(input.subsequence(0, input.len() - 1), radix)
            + input[input.len() - 1]@ }
    }
}

/// Little-endian radix evaluation of the active implementation digits.
#[logic(open)]
#[variant(input.len())]
pub fn le(input: Seq<u8>, radix: Int) -> Int {
    pearlite! {
        if input.len() == 0 { 0 }
        else { input[0]@ + radix * le(input.subsequence(1, input.len()), radix) }
    }
}

/// Total lookup; 255 is an invalid-input marker, never a valid radix-58 digit.
#[logic(open)]
pub fn digit(decode: Seq<u8>, c: u8) -> Int {
    pearlite! {
        if decode.len() == 128 && c@ < 128 { decode[c@]@ } else { 255 }
    }
}

#[logic(open)]
#[variant(input.len())]
pub fn be58(input: Seq<u8>, decode: Seq<u8>) -> Int {
    pearlite! {
        if input.len() == 0 { 0 }
        else { 58 * be58(input.subsequence(0, input.len() - 1), decode)
            + digit(decode, input[input.len() - 1]) }
    }
}

#[logic(open)]
#[variant(input.len())]
pub fn leading(input: Seq<u8>, zero: u8) -> Int {
    pearlite! {
        if input.len() == 0 || input[0] != zero { 0 }
        else { 1 + leading(input.subsequence(1, input.len()), zero) }
    }
}

#[logic(open)]
pub fn good_prefix(input: Seq<u8>, decode: Seq<u8>, n: Int) -> bool {
    pearlite! {
        0 <= n && n <= input.len()
        && forall<i: Int> 0 <= i && i < n ==> digit(decode, input[i]) < 58
    }
}

#[logic(open)]
pub fn valid_base(base: Seq<u8>, n: Int) -> bool {
    pearlite! {
        0 <= n && n <= base.len()
        && (forall<i: Int> 0 <= i && i < n ==> base[i]@ < 128)
        && (forall<i: Int, j: Int> 0 <= i && i < j && j < n ==> base[i] != base[j])
    }
}

#[logic(open)]
pub fn valid_alphabet(encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! {
        encode.len() == 58 && decode.len() == 128
        && valid_base(encode, 58)
        && (forall<i: Int> 0 <= i && i < 58 ==> decode[encode[i]@]@ == i)
        && (forall<c: Int> 0 <= c && c < 128 ==>
            decode[c]@ == 255 ||
            (decode[c]@ < 58 && encode[decode[c]@]@ == c))
    }
}

/// Constructor invariant: the inverse table is exact for the processed prefix.
#[logic(open)]
pub fn alphabet_prefix(base: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>, n: Int) -> bool {
    pearlite! {
        base.len() == 58 && encode.len() == 58 && decode.len() == 128
        && valid_base(base, n)
        && (forall<i: Int> 0 <= i && i < n ==> encode[i] == base[i])
        && (forall<c: Int> 0 <= c && c < 128 ==>
            (decode[c]@ == 255 && (forall<i: Int> 0 <= i && i < n ==> base[i]@ != c))
            || (decode[c]@ < n && base[decode[c]@]@ == c))
    }
}

#[logic(open)]
pub fn alphabet_result(base: Seq<u8>, result: Result<Alphabet, AlphabetError>) -> bool {
    pearlite! {
        base.len() == 58 && match result {
            Ok(alpha) => alpha.encode@ == base && valid_alphabet(alpha.encode@, alpha.decode@),
            Err(AlphabetError::NonAsciiCharacter { index }) =>
                index@ < 58 && valid_base(base, index@) && base[index@]@ >= 128,
            Err(AlphabetError::DuplicateCharacter { character, first, second }) =>
                first@ < second@ && second@ < 58 && valid_base(base, second@)
                && base[second@]@ < 128 && base[first@] == base[second@]
                && character@ == base[second@]@,
        }
    }
}

/// Canonical base-radix width, with width zero for the integer zero.
#[logic(open)]
pub fn width(value: Int, radix: Int, n: Int) -> bool {
    pearlite! {
        radix >= 2 && n >= 0 &&
        ((value == 0 && n == 0) ||
         (value > 0 && n > 0 && pow(radix, n - 1) <= value && value < pow(radix, n)))
    }
}

#[logic(open)]
pub fn encode_fits(input: Seq<u8>, capacity: Int) -> bool {
    pearlite! {
        leading(input, 0u8) <= capacity
        && be(input, 256) < pow(58, capacity - leading(input, 0u8))
    }
}

#[logic(open)]
pub fn decode_fits(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>, capacity: Int) -> bool {
    pearlite! {
        encode.len() == 58 && good_prefix(input, decode, input.len())
        && leading(input, encode[0]) <= capacity
        && be58(input, decode) < pow(256, capacity - leading(input, encode[0]))
    }
}

#[logic(open)]
pub fn encoded(input: Seq<u8>, encoded: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! {
        encode.len() == 58 && good_prefix(encoded, decode, encoded.len())
        && leading(encoded, encode[0]) == leading(input, 0u8)
        && be58(encoded, decode) == be(input, 256)
    }
}

#[logic(open)]
pub fn decoded(input: Seq<u8>, decoded: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! {
        encode.len() == 58 && good_prefix(input, decode, input.len())
        && leading(decoded, 0u8) == leading(input, encode[0])
        && be(decoded, 256) == be58(input, decode)
    }
}

#[logic(open)]
pub fn unchanged_suffix(before: Seq<u8>, after: Seq<u8>, n: Int) -> bool {
    pearlite! {
        before.len() == after.len() && 0 <= n && n <= before.len()
        && forall<i: Int> n <= i && i < before.len() ==> after[i] == before[i]
    }
}

#[logic(open)]
pub fn encode_result(input: Seq<u8>, before: Seq<u8>, after: Seq<u8>,
    encode: Seq<u8>, decode: Seq<u8>, result: Result<usize, EncodeError>) -> bool {
    pearlite! {
        before.len() == after.len() && match result {
            Ok(n) => n@ <= after.len() && encode_fits(input, before.len())
                && encoded(input, after.subsequence(0, n@), encode, decode)
                && unchanged_suffix(before, after, n@),
            Err(EncodeError::BufferTooSmall) => !encode_fits(input, before.len()),
        }
    }
}

/// Exact error precedence: magnitude growth can exhaust the buffer before a
/// later invalid byte. Leading zero symbols consume space only after validation.
#[logic(open)]
pub fn decode_error(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>, capacity: Int,
    error: DecodeError) -> bool {
    pearlite! {
        match error {
            DecodeError::BufferTooSmall =>
                (exists<j: Int> 0 <= j && j <= input.len()
                    && good_prefix(input, decode, j)
                    && be58(input.subsequence(0, j), decode) >= pow(256, capacity))
                || (good_prefix(input, decode, input.len())
                    && !decode_fits(input, encode, decode, capacity)),
            DecodeError::NonAsciiCharacter { index } =>
                index@ < input.len() && good_prefix(input, decode, index@)
                && input[index@]@ >= 128
                && be58(input.subsequence(0, index@), decode) < pow(256, capacity),
            DecodeError::InvalidCharacter { character, index } =>
                index@ < input.len() && good_prefix(input, decode, index@)
                && input[index@]@ < 128 && digit(decode, input[index@]) == 255
                && character@ == input[index@]@
                && be58(input.subsequence(0, index@), decode) < pow(256, capacity),
        }
    }
}

#[logic(open)]
pub fn decode_result(input: Seq<u8>, before: Seq<u8>, after: Seq<u8>,
    encode: Seq<u8>, decode: Seq<u8>, result: Result<usize, DecodeError>) -> bool {
    pearlite! {
        before.len() == after.len() && match result {
            Ok(n) => n@ <= after.len() && decode_fits(input, encode, decode, before.len())
                && decoded(input, after.subsequence(0, n@), encode, decode)
                && unchanged_suffix(before, after, n@),
            Err(error) => decode_error(input, encode, decode, before.len(), error),
        }
    }
}

#[logic(open)]
pub fn decode_const_result<const N: usize>(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>,
    result: Result<[u8; N], DecodeError>) -> bool {
    pearlite! {
        match result {
            Ok(output) => decode_fits(input, encode, decode, N@)
                && (exists<n: Int> 0 <= n && n <= N@
                    && decoded(input, output@.subsequence(0, n), encode, decode)
                    && (forall<i: Int> n <= i && i < N@ ==> output@[i] == 0u8)),
            Err(error) => decode_error(input, encode, decode, N@, error),
        }
    }
}

// These are checked mathematical lemmas, not axioms or trusted declarations.
// Their proof obligations belong in the complete verification inventory.

#[logic(opaque)]
#[requires(0 <= n && n < input.len())]
#[ensures(result && be(input.subsequence(0, n + 1), radix)
    == radix * be(input.subsequence(0, n), radix) + input[n]@)]
pub fn be_step(input: Seq<u8>, radix: Int, n: Int) -> bool {
    pearlite! {
        input.subsequence(0, n + 1).subsequence(0, n)
            == input.subsequence(0, n)
        && input.subsequence(0, n + 1)[n] == input[n]
        && be(input.subsequence(0, n + 1), radix)
            == radix * be(input.subsequence(0, n), radix) + input[n]@
    }
}

#[logic(opaque)]
#[requires(0 <= n && n < input.len())]
#[ensures(result && be58(input.subsequence(0, n + 1), decode)
    == 58 * be58(input.subsequence(0, n), decode) + digit(decode, input[n]))]
pub fn be58_step(input: Seq<u8>, decode: Seq<u8>, n: Int) -> bool {
    pearlite! {
        input.subsequence(0, n + 1).subsequence(0, n)
            == input.subsequence(0, n)
        && input.subsequence(0, n + 1)[n] == input[n]
        && be58(input.subsequence(0, n + 1), decode)
            == 58 * be58(input.subsequence(0, n), decode) + digit(decode, input[n])
    }
}

#[logic(opaque)]
#[requires(0 <= n && n <= input.len())]
#[variant(n)]
#[ensures(result && le(input, radix) == le(input.subsequence(0, n), radix)
    + pow(radix, n) * le(input.subsequence(n, input.len()), radix))]
pub fn le_split(input: Seq<u8>, radix: Int, n: Int) -> bool {
    pearlite! {
        if n == 0 {
            input.subsequence(0, n).len() == 0
                && input.subsequence(n, input.len()) == input
                && pow(radix, n) == 1
                && le(input, radix) == le(input.subsequence(0, n), radix)
                + pow(radix, n) * le(input.subsequence(n, input.len()), radix)
        } else {
            le_split(input.subsequence(1, input.len()), radix, n - 1)
                && input.subsequence(1, input.len()).len() == input.len() - 1
                && input.subsequence(0, n).len() == n
                && input.subsequence(0, n)[0] == input[0]
                && input.subsequence(0, n).subsequence(1, n)
                    == input.subsequence(1, input.len()).subsequence(0, n - 1)
                && input.subsequence(0, n)
                    .subsequence(1, input.subsequence(0, n).len())
                    == input.subsequence(1, input.len()).subsequence(0, n - 1)
                && input.subsequence(1, input.len())
                    .subsequence(n - 1, input.len() - 1)
                    == input.subsequence(n, input.len())
                && input.subsequence(1, input.len())
                    .subsequence(n - 1, input.subsequence(1, input.len()).len())
                    == input.subsequence(n, input.len())
                && pow(radix, n) == radix * pow(radix, n - 1)
                && le(input, radix) == input[0]@ + radix
                    * le(input.subsequence(1, input.len()), radix)
                && crate::lemmas::le_prefix_head(input, radix, n)
                && le(input.subsequence(1, input.len()), radix)
                    == le(input.subsequence(1, input.len())
                        .subsequence(0, n - 1), radix)
                        + pow(radix, n - 1) * le(input.subsequence(n, input.len()), radix)
                && radix * (le(input.subsequence(1, input.len())
                    .subsequence(0, n - 1), radix)
                    + pow(radix, n - 1) * le(input.subsequence(n, input.len()), radix))
                    == radix * le(input.subsequence(1, input.len())
                        .subsequence(0, n - 1), radix)
                        + pow(radix, n) * le(input.subsequence(n, input.len()), radix)
                && crate::lemmas::le_split_algebra(
                    le(input, radix), le(input.subsequence(0, n), radix),
                    le(input.subsequence(1, input.len()), radix),
                    le(input.subsequence(1, input.len()).subsequence(0, n - 1), radix),
                    le(input.subsequence(n, input.len()), radix),
                    input[0]@, radix, pow(radix, n - 1), pow(radix, n))
        }
    }
}

#[logic(opaque)]
#[requires(radix >= 2 && n >= 0)]
#[variant(n)]
#[ensures(result && pow(radix, n) >= 1)]
pub fn pow_positive(radix: Int, n: Int) -> bool {
    pearlite! {
        if n == 0 { pow(radix, n) >= 1 }
        else { pow_positive(radix, n - 1) && pow(radix, n) >= 1 }
    }
}
