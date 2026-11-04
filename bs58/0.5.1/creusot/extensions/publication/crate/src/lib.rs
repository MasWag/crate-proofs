#![no_std]
extern crate alloc;
pub mod vec_utils;

// Verification fork of bs58 0.5.1. Runtime adaptations from the release are
// documented in ../correspondence.md. No application computation is trusted.
#[cfg(creusot)]
use creusot_std::prelude::{check, ensures, invariant, proof_assert, requires, Int};

#[cfg(creusot)]
pub mod spec;
#[cfg(creusot)]
pub mod lemmas;
#[cfg(creusot)]
pub mod encoder_lemmas;

/// Prepared Base58 alphabet. The tables have the same representation as bs58.
#[cfg_attr(not(creusot), derive(Clone, Copy, Debug, Eq, PartialEq))]
pub struct Alphabet {
    pub encode: [u8; 58],
    pub decode: [u8; 128],
}

#[cfg_attr(not(creusot), derive(Clone, Copy, Debug, Eq, PartialEq))]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel, creusot_std::prelude::PartialEq, Copy))]
pub enum AlphabetError {
    DuplicateCharacter { character: char, first: usize, second: usize },
    NonAsciiCharacter { index: usize },
}

impl Alphabet {
    #[cfg_attr(creusot, check(terminates))]
    #[cfg_attr(creusot, ensures(spec::alphabet_result(base@, result)))]
    pub const fn new(base: &[u8; 58]) -> Result<Self, AlphabetError> {
        let mut encode = [0x00; 58];
        let mut decode = [0xFF; 128];

        let mut i = 0;
        #[cfg_attr(creusot, invariant(spec::alphabet_prefix(base@, encode@, decode@, i@)))]
        #[cfg_attr(creusot, variant(58 - i@))]
        while i < encode.len() {
            if base[i] >= 128 {
                return Err(AlphabetError::NonAsciiCharacter { index: i });
            }
            if decode[base[i] as usize] != 0xFF {
                return Err(AlphabetError::DuplicateCharacter {
                    character: base[i] as char,
                    first: decode[base[i] as usize] as usize,
                    second: i,
                });
            }
            encode[i] = base[i];
            decode[base[i] as usize] = i as u8;
            i += 1;
        }

        #[cfg(creusot)]
        {
            proof_assert!(i@ == 58);
            proof_assert!(encode@ == base@);
            proof_assert!(forall<j: Int> 0 <= j && j < 58 ==>
                decode@[encode@[j]@]@ == j);
            proof_assert!(spec::valid_alphabet(encode@, decode@));
        }
        Ok(Self { encode, decode })
    }
}

#[cfg_attr(not(creusot), derive(Clone, Copy, Debug, Eq, PartialEq))]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel, creusot_std::prelude::PartialEq, Copy))]
pub enum EncodeError {
    BufferTooSmall,
}

#[cfg_attr(not(creusot), derive(Clone, Copy, Debug, Eq, PartialEq))]
#[cfg_attr(creusot, derive(creusot_std::prelude::DeepModel, creusot_std::prelude::PartialEq, Copy))]
pub enum DecodeError {
    BufferTooSmall,
    InvalidCharacter { character: char, index: usize },
    NonAsciiCharacter { index: usize },
}

/// Encode input into `output`, returning the occupied prefix length.
/// The arithmetic and output writes follow bs58 0.5.1 `encode_into`.
#[cfg_attr(creusot, check(terminates))]
#[cfg_attr(creusot, requires(spec::valid_alphabet(alpha.encode@, alpha.decode@)))]
#[cfg_attr(creusot, ensures(spec::encode_result(input@, output@, (^output)@,
    alpha.encode@, alpha.decode@, result)))]
pub fn encode_into(input: &[u8], output: &mut [u8], alpha: &Alphabet) -> Result<usize, EncodeError> {
    #[cfg(creusot)]
    let original = creusot_std::prelude::snapshot!(output@);
    let mut index = 0;
    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && 0 <= index@ && index@ <= output@.len()
        && spec::le(output@.subsequence(0, index@), 58)
            == spec::be(input@.subsequence(0, i@), 256)
        && (forall<k: Int> 0 <= k && k < index@ ==> output@[k]@ < 58)
        && (index@ == 0 || output@[index@ - 1] != 0u8)
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(input@.len() - i@))]
    while i < input.len() {
        #[cfg(creusot)]
        proof_assert!(spec::be_step(input@, 256, i@));
        let mut carry = input[i] as usize;
        let mut j = 0;
        #[cfg_attr(creusot, invariant(0 <= j@ && j@ <= index@
            && 0 <= carry@ && carry@ <= 255
            && 0 <= index@ && index@ <= output@.len()
            && spec::le(output@.subsequence(0, j@), 58)
                + spec::pow(58, j@) * carry@
                + 256 * spec::pow(58, j@)
                    * spec::le(output@.subsequence(j@, index@), 58)
                == spec::be(input@.subsequence(0, i@ + 1), 256)
            && (forall<k: Int> 0 <= k && k < index@ ==> output@[k]@ < 58)
            && (j@ < index@ ==> output@[index@ - 1] != 0u8)
            && (index@ == 0 || j@ < index@ || carry@ > 0)
            && spec::unchanged_suffix(*original, output@, index@)))]
        #[cfg_attr(creusot, variant(index@ - j@))]
        while j < index {
            #[cfg(creusot)]
            let before = creusot_std::prelude::snapshot!(output@);
            #[cfg(creusot)]
            let position = creusot_std::prelude::snapshot!(j@);
            #[cfg(creusot)]
            let incoming = creusot_std::prelude::snapshot!(carry@);
            carry += (output[j] as usize) * 256;
            output[j] = (carry % 58) as u8;
            carry /= 58;
            j += 1;
            #[cfg(creusot)]
            {
                proof_assert!(encoder_lemmas::le_extend(*before, output@, 58, *position));
                proof_assert!((*before).subsequence(*position, index@).subsequence(1, index@ - *position)
                    == output@.subsequence(j@, index@));
                proof_assert!(spec::le((*before).subsequence(*position, index@), 58)
                    == (*before)[*position]@ + 58 * spec::le(output@.subsequence(j@, index@), 58));
                proof_assert!(spec::le(output@.subsequence(0, j@), 58)
                    == spec::le((*before).subsequence(0, *position), 58)
                        + spec::pow(58, *position) * output@[*position]@);
                proof_assert!(spec::pow(58, j@) == 58 * spec::pow(58, *position));
                proof_assert!(output@[*position]@ == (*incoming + 256 * (*before)[*position]@) % 58);
                proof_assert!(carry@ == (*incoming + 256 * (*before)[*position]@) / 58);
                proof_assert!(encoder_lemmas::horner_weight(
                    spec::le((*before).subsequence(0, *position), 58),
                    spec::pow(58, *position), *incoming, (*before)[*position]@,
                    spec::le(output@.subsequence(j@, index@), 58)));
                creusot_std::prelude::ghost! {
                    let a = creusot_std::prelude::snapshot!(spec::le((*before).subsequence(0, *position), 58));
                    let p = creusot_std::prelude::snapshot!(spec::pow(58, *position));
                    let d = creusot_std::prelude::snapshot!((*before)[*position]@);
                    let t = creusot_std::prelude::snapshot!(spec::le((*before).subsequence(*position, index@), 58));
                    let b = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(0, j@), 58));
                    let q = creusot_std::prelude::snapshot!(spec::pow(58, j@));
                    let c = creusot_std::prelude::snapshot!(carry@);
                    let e = creusot_std::prelude::snapshot!(output@[*position]@);
                    let u = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(j@, index@), 58));
                    encoder_lemmas::horner_step(a, p, incoming, d, t, b, q, c, e, u);
                };
                proof_assert!(spec::le(output@.subsequence(0, j@), 58)
                    + spec::pow(58, j@) * carry@
                    + 256 * spec::pow(58, j@) * spec::le(output@.subsequence(j@, index@), 58)
                    == spec::le((*before).subsequence(0, *position), 58)
                        + spec::pow(58, *position) * *incoming
                        + 256 * spec::pow(58, *position) * spec::le((*before).subsequence(*position, index@), 58));
            }
        }
        #[cfg(creusot)]
        {
            proof_assert!(j@ == index@);
            proof_assert!(output@.subsequence(j@, index@).len() == 0);
            proof_assert!(spec::le(output@.subsequence(j@, index@), 58) == 0);
        }
        #[cfg_attr(creusot, invariant(0 <= index@ && index@ <= output@.len()
            && 0 <= carry@ && carry@ <= 255
            && spec::le(output@.subsequence(0, index@), 58)
                + spec::pow(58, index@) * carry@
                == spec::be(input@.subsequence(0, i@ + 1), 256)
            && (forall<k: Int> 0 <= k && k < index@ ==> output@[k]@ < 58)
            && (carry@ > 0 || index@ == 0 || output@[index@ - 1] != 0u8)
            && spec::unchanged_suffix(*original, output@, index@)))]
        #[cfg_attr(creusot, variant(carry@))]
        while carry > 0 {
            if index == output.len() {
                #[cfg(creusot)]
                proof_assert!(encoder_lemmas::encode_growth_failure(input@, output@, i@ + 1, index@, carry@));
                return Err(EncodeError::BufferTooSmall);
            }
            #[cfg(creusot)]
            let before = creusot_std::prelude::snapshot!(output@);
            #[cfg(creusot)]
            let position = creusot_std::prelude::snapshot!(index@);
            #[cfg(creusot)]
            let incoming = creusot_std::prelude::snapshot!(carry@);
            output[index] = (carry % 58) as u8;
            index += 1;
            carry /= 58;
            #[cfg(creusot)]
            {
                proof_assert!(encoder_lemmas::le_extend(*before, output@, 58, *position));
                proof_assert!(spec::le(output@.subsequence(0, index@), 58)
                    == spec::le((*before).subsequence(0, *position), 58)
                        + spec::pow(58, *position) * output@[*position]@);
                proof_assert!(spec::pow(58, index@) == 58 * spec::pow(58, *position));
                proof_assert!(output@[*position]@ == *incoming % 58);
                proof_assert!(carry@ == *incoming / 58);
                proof_assert!(encoder_lemmas::division_weight(spec::pow(58, *position), *incoming));
                creusot_std::prelude::ghost! {
                    let a = creusot_std::prelude::snapshot!(spec::le((*before).subsequence(0, *position), 58));
                    let p = creusot_std::prelude::snapshot!(spec::pow(58, *position));
                    let b = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(0, index@), 58));
                    let q = creusot_std::prelude::snapshot!(spec::pow(58, index@));
                    let c = creusot_std::prelude::snapshot!(carry@);
                    let d = creusot_std::prelude::snapshot!(output@[*position]@);
                    encoder_lemmas::append_step(a, p, incoming, b, q, c, d);
                };
                proof_assert!(spec::le(output@.subsequence(0, index@), 58)
                    + spec::pow(58, index@) * carry@
                    == spec::le((*before).subsequence(0, *position), 58)
                        + spec::pow(58, *position) * *incoming);
            }
        }
        i += 1;
    }
    #[cfg(creusot)]
    proof_assert!(input@.subsequence(0, i@) == input@);

    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && 0 <= index@ && index@ <= output@.len()
        && i@ <= index@
        && (forall<k: Int> 0 <= k && k < i@ ==> input@[k] == 0u8)
        && spec::le(output@.subsequence(0, index@), 58) == spec::be(input@, 256)
        && (forall<k: Int> 0 <= k && k < index@ ==> output@[k]@ < 58)
        && (forall<k: Int> index@ - i@ <= k && k < index@ ==> output@[k] == 0u8)
        && (index@ == i@ || output@[index@ - i@ - 1] != 0u8)
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(input@.len() - i@))]
    while i < input.len() && input[i] == 0 {
        if index == output.len() {
            #[cfg(creusot)]
            proof_assert!(encoder_lemmas::encode_zero_failure(input@, output@, i@, index@));
            return Err(EncodeError::BufferTooSmall);
        }
        #[cfg(creusot)]
        let before = creusot_std::prelude::snapshot!(output@);
        #[cfg(creusot)]
        let position = creusot_std::prelude::snapshot!(index@);
        output[index] = 0;
        index += 1;
        i += 1;
        #[cfg(creusot)]
        proof_assert!(encoder_lemmas::le_extend(*before, output@, 58, *position));
    }
    #[cfg(creusot)]
    proof_assert!(lemmas::leading_exact(input@, 0u8, i@, input@.len()));
    #[cfg(creusot)]
    {
        proof_assert!(input@.subsequence(0, input@.len()) == input@);
        proof_assert!(i@ == spec::leading(input@, 0u8));
        proof_assert!(encoder_lemmas::encode_success_fits(input@, output@, i@, index@));
    }
    #[cfg(creusot)]
    let zeros = creusot_std::prelude::snapshot!(i@);

    #[cfg(creusot)]
    let digits = creusot_std::prelude::snapshot!(output@);
    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= index@ && index@ <= output@.len()
        && index@ <= (*digits).len()
        && spec::le((*digits).subsequence(0, index@), 58) == spec::be(input@, 256)
        && *zeros == spec::leading(input@, 0u8) && 0 <= *zeros && *zeros <= index@
        && (forall<k: Int> index@ - *zeros <= k && k < index@ ==>
            (*digits)[k] == 0u8)
        && (index@ == *zeros || (*digits)[index@ - *zeros - 1] != 0u8)
        && (forall<k: Int> 0 <= k && k < index@ ==> (*digits)[k]@ < 58)
        && (forall<k: Int> 0 <= k && k < i@ ==>
            output@[k] == alpha.encode@[(*digits)[k]@])
        && (forall<k: Int> i@ <= k && k < index@ ==> output@[k] == (*digits)[k])
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(index@ - i@))]
    while i < index {
        output[i] = alpha.encode[output[i] as usize];
        i += 1;
    }

    #[cfg(creusot)]
    let mapped = creusot_std::prelude::snapshot!(output@);
    let mut i = 0;
    let n = index / 2;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= n@ && n@ == index@ / 2
        && 0 <= index@ && index@ <= output@.len()
        && index@ <= (*digits).len() && index@ <= (*mapped).len()
        && *zeros == spec::leading(input@, 0u8) && 0 <= *zeros && *zeros <= index@
        && spec::le((*digits).subsequence(0, index@), 58) == spec::be(input@, 256)
        && (forall<k: Int> 0 <= k && k < index@ ==> (*digits)[k]@ < 58)
        && (forall<k: Int> index@ - *zeros <= k && k < index@ ==>
            (*digits)[k] == 0u8)
        && (index@ == *zeros || (*digits)[index@ - *zeros - 1] != 0u8)
        && (forall<k: Int> 0 <= k && k < index@ ==>
            (*mapped)[k] == alpha.encode@[(*digits)[k]@])
        && (forall<k: Int> 0 <= k && k < i@ ==>
            output@[k] == (*mapped)[index@ - 1 - k])
        && (forall<k: Int> i@ <= k && k < index@ - i@ ==>
            output@[k] == (*mapped)[k])
        && (forall<k: Int> index@ - i@ <= k && k < index@ ==>
            output@[k] == (*mapped)[index@ - 1 - k])
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(n@ - i@))]
    while i < n {
        let x = output[i];
        output[i] = output[index - 1 - i];
        output[index - 1 - i] = x;
        i += 1;
    }
    #[cfg(creusot)]
    {
        proof_assert!(forall<k: Int> 0 <= k && k < index@ ==>
            output@[k] == (*mapped)[index@ - 1 - k]);
        proof_assert!(forall<k: Int> 0 <= k && k < index@ ==>
            spec::digit(alpha.decode@, output@[k]) == (*digits)[index@ - 1 - k]@);
        proof_assert!(spec::good_prefix(output@.subsequence(0, index@), alpha.decode@, index@));
        proof_assert!(forall<k: Int> index@ - *zeros <= k && k < index@ ==>
            (*mapped)[k] == alpha.encode@[0]);
        proof_assert!(index@ == *zeros || (*mapped)[index@ - *zeros - 1] != alpha.encode@[0]);
        proof_assert!(lemmas::alphabet_reverse_value(
            *digits, *mapped, output@, alpha.encode@, alpha.decode@, index@
        ));
        proof_assert!(lemmas::leading_reverse(
            *mapped, output@, alpha.encode[0], *zeros, index@
        ));
        proof_assert!(encoder_lemmas::encode_success_fits(input@, *digits, *zeros, index@));
        proof_assert!(spec::encode_fits(input@, output@.len()));
        proof_assert!(spec::be58(output@.subsequence(0, index@), alpha.decode@)
            == spec::be(input@, 256));
        proof_assert!(spec::leading(output@.subsequence(0, index@), alpha.encode@[0]) == *zeros);
        proof_assert!(spec::encoded(input@, output@.subsequence(0, index@), alpha.encode@, alpha.decode@));
    }
    Ok(index)
}

/// Decode input into `output`, returning the occupied prefix length.
/// The arithmetic and output writes follow bs58 0.5.1 `decode_into`.
#[cfg_attr(creusot, check(terminates))]
#[cfg_attr(creusot, requires(spec::valid_alphabet(alpha.encode@, alpha.decode@)))]
#[cfg_attr(creusot, ensures(spec::decode_result(input@, output@, (^output)@,
    alpha.encode@, alpha.decode@, result)))]
pub fn decode_into(input: &[u8], output: &mut [u8], alpha: &Alphabet) -> Result<usize, DecodeError> {
    #[cfg(creusot)]
    let original = creusot_std::prelude::snapshot!(output@);
    let mut index = 0;
    let zero = alpha.encode[0];

    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && spec::good_prefix(input@, alpha.decode@, i@)
        && 0 <= index@ && index@ <= output@.len()
        && spec::le(output@.subsequence(0, index@), 256)
            == spec::be58(input@.subsequence(0, i@), alpha.decode@)
        && (index@ == 0 || output@[index@ - 1] != 0u8)
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(input@.len() - i@))]
    while i < input.len() {
        let c = input[i];
        if c > 127 {
            #[cfg(creusot)]
            {
                proof_assert!(lemmas::le_bound(output@.subsequence(0, index@), 256));
                proof_assert!(lemmas::pow_monotone(256, index@, output@.len()));
            }
            return Err(DecodeError::NonAsciiCharacter { index: i });
        }
        let mut val = alpha.decode[c as usize] as usize;
        if val == 0xFF {
            #[cfg(creusot)]
            {
                proof_assert!(lemmas::le_bound(output@.subsequence(0, index@), 256));
                proof_assert!(lemmas::pow_monotone(256, index@, output@.len()));
            }
            return Err(DecodeError::InvalidCharacter {
                character: c as char,
                index: i,
            });
        }
        #[cfg(creusot)]
        proof_assert!(spec::be58_step(input@, alpha.decode@, i@));
        #[cfg(creusot)]
        let old_digits = creusot_std::prelude::snapshot!(output@);
        #[cfg(creusot)]
        let old_index = index;
        let mut j = 0;
        #[cfg_attr(creusot, invariant(0 <= i@ && i@ < input@.len()
            && spec::good_prefix(input@, alpha.decode@, i@ + 1)
            && 0 <= j@ && j@ <= index@
            && old_index@ == index@
            && spec::le((*old_digits).subsequence(0, index@), 256)
                == spec::be58(input@.subsequence(0, i@), alpha.decode@)
            && (index@ == 0 || (*old_digits)[index@ - 1] != 0u8)
            && 0 <= val@ && val@ <= 57
            && 0 <= index@ && index@ <= output@.len()
            && spec::le(output@.subsequence(0, j@), 256)
                + spec::pow(256, j@) * val@
                + 58 * spec::pow(256, j@)
                    * spec::le(output@.subsequence(j@, index@), 256)
                == spec::be58(input@.subsequence(0, i@ + 1), alpha.decode@)
            && spec::unchanged_suffix(*original, output@, index@)))]
        #[cfg_attr(creusot, variant(index@ - j@))]
        while j < index {
            #[cfg(creusot)]
            let before = creusot_std::prelude::snapshot!(output@);
            #[cfg(creusot)]
            let position = creusot_std::prelude::snapshot!(j@);
            #[cfg(creusot)]
            let old_carry = val;
            let byte = output[j];
            val += (byte as usize) * 58;
            output[j] = (val % 256) as u8;
            val /= 256;
            j += 1;
            #[cfg(creusot)]
            {
                proof_assert!(j@ == *position + 1);
                proof_assert!(encoder_lemmas::le_extend(*before, output@, 256, *position));
                proof_assert!(spec::le_split(
                    (*before).subsequence(*position, index@), 256, 1
                ));
                proof_assert!(old_carry@ + (*before)[*position]@ * 58
                    == val@ * 256 + output@[*position]@);
                proof_assert!((*before).subsequence(j@, index@)
                    == output@.subsequence(j@, index@));
                creusot_std::prelude::ghost! {
                    let old = creusot_std::prelude::snapshot!(*before);
                    let new = creusot_std::prelude::snapshot!(output@);
                    let pos = creusot_std::prelude::snapshot!(*position);
                    let next = creusot_std::prelude::snapshot!(j@);
                    let end = creusot_std::prelude::snapshot!(index@);
                    lemmas::decode_tail_step(old, new, pos, next, end);
                };
                proof_assert!(spec::pow(256, j@) == 256 * spec::pow(256, *position));
                proof_assert!(spec::le((*before).subsequence(*position, index@), 256)
                    == (*before)[*position]@
                        + 256 * spec::le(output@.subsequence(j@, index@), 256));
                proof_assert!(lemmas::decode_carry_step(
                    spec::le((*before).subsequence(0, *position), 256),
                    spec::pow(256, *position), old_carry@, (*before)[*position]@,
                    spec::le((*before).subsequence(*position, index@), 256),
                    spec::le(output@.subsequence(0, j@), 256),
                    spec::pow(256, j@), val@, output@[*position]@,
                    spec::le(output@.subsequence(j@, index@), 256)
                ));
                creusot_std::prelude::ghost! {
                    let a = creusot_std::prelude::snapshot!(spec::le((*before).subsequence(0, *position), 256));
                    let p = creusot_std::prelude::snapshot!(spec::pow(256, *position));
                    let c = creusot_std::prelude::snapshot!(old_carry@);
                    let d = creusot_std::prelude::snapshot!((*before)[*position]@);
                    let t = creusot_std::prelude::snapshot!(spec::le((*before).subsequence(*position, index@), 256));
                    let b = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(0, j@), 256));
                    let q = creusot_std::prelude::snapshot!(spec::pow(256, j@));
                    let e = creusot_std::prelude::snapshot!(val@);
                    let f = creusot_std::prelude::snapshot!(output@[*position]@);
                    let u = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(j@, index@), 256));
                    lemmas::decode_horner_step(a, p, c, d, t, b, q, e, f, u);
                };
                proof_assert!(spec::le(output@.subsequence(0, j@), 256)
                    + spec::pow(256, j@) * val@
                    + 58 * spec::pow(256, j@)
                        * spec::le(output@.subsequence(j@, index@), 256)
                    == spec::le((*before).subsequence(0, *position), 256)
                        + spec::pow(256, *position) * old_carry@
                        + 58 * spec::pow(256, *position)
                            * spec::le((*before).subsequence(*position, index@), 256));
            }
        }
        #[cfg(creusot)]
        {
            proof_assert!(j@ == index@);
            proof_assert!(spec::le(output@.subsequence(j@, index@), 256) == 0);
        }
        #[cfg(creusot)]
        if val == 0 && index > 0 {
            proof_assert!(lemmas::decode_canonical_growth(
                *old_digits, output@, index@,
                spec::digit(alpha.decode@, c)
            ));
        }
        #[cfg_attr(creusot, invariant(0 <= i@ && i@ < input@.len()
            && spec::good_prefix(input@, alpha.decode@, i@ + 1)
            && 0 <= index@ && index@ <= output@.len()
            && old_index@ <= index@ && index@ <= old_index@ + 1
            && (val@ > 0 ==> index@ == old_index@)
            && (val@ == 0 ==> (index@ == 0 || output@[index@ - 1] != 0u8))
            && 0 <= val@ && val@ <= 57
            && spec::le(output@.subsequence(0, index@), 256)
                + spec::pow(256, index@) * val@
                == spec::be58(input@.subsequence(0, i@ + 1), alpha.decode@)
            && spec::unchanged_suffix(*original, output@, index@)))]
        #[cfg_attr(creusot, variant(val@))]
        while val > 0 {
            if index >= output.len() {
                #[cfg(creusot)]
                {
                    proof_assert!(index@ == output@.len());
                    proof_assert!(output@.subsequence(0, index@).len() == index@);
                    proof_assert!(lemmas::decode_growth_failure(
                        input@, output@.subsequence(0, index@),
                        alpha.decode@, i@ + 1, index@, val@
                    ));
                    proof_assert!(spec::be58(input@.subsequence(0, i@ + 1), alpha.decode@)
                        >= spec::pow(256, index@));
                    proof_assert!(spec::pow(256, index@)
                        == spec::pow(256, output@.len()));
                }
                #[cfg(creusot)]
                proof_assert!(exists<consumed: Int> consumed == i@ + 1
                    && spec::good_prefix(input@, alpha.decode@, consumed)
                    && spec::be58(input@.subsequence(0, consumed), alpha.decode@)
                        >= spec::pow(256, output@.len()));
                return Err(DecodeError::BufferTooSmall);
            }
            #[cfg(creusot)]
            let before = creusot_std::prelude::snapshot!(output@);
            #[cfg(creusot)]
            let position = creusot_std::prelude::snapshot!(index@);
            #[cfg(creusot)]
            let incoming = creusot_std::prelude::snapshot!(val@);
            output[index] = (val % 256) as u8;
            index += 1;
            val /= 256;
            #[cfg(creusot)]
            {
                proof_assert!(encoder_lemmas::le_extend(*before, output@, 256, *position));
                proof_assert!(spec::le(output@.subsequence(0, index@), 256)
                    == spec::le((*before).subsequence(0, *position), 256)
                        + spec::pow(256, *position) * output@[*position]@);
                proof_assert!(spec::pow(256, index@) == 256 * spec::pow(256, *position));
                proof_assert!(output@[*position]@ == *incoming % 256);
                proof_assert!(val@ == *incoming / 256);
                creusot_std::prelude::ghost! {
                    let a = creusot_std::prelude::snapshot!(spec::le((*before).subsequence(0, *position), 256));
                    let p = creusot_std::prelude::snapshot!(spec::pow(256, *position));
                    let b = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(0, index@), 256));
                    let q = creusot_std::prelude::snapshot!(spec::pow(256, index@));
                    let c = creusot_std::prelude::snapshot!(val@);
                    let d = creusot_std::prelude::snapshot!(output@[*position]@);
                    lemmas::decode_append_step(a, p, incoming, b, q, c, d);
                };
                proof_assert!(spec::le(output@.subsequence(0, index@), 256)
                    + spec::pow(256, index@) * val@
                    == spec::le((*before).subsequence(0, *position), 256)
                        + spec::pow(256, *position) * *incoming);
                proof_assert!(val@ == 0);
                proof_assert!(output@[index@ - 1] != 0u8);
            }
        }
        i += 1;
    }

    #[cfg(creusot)]
    {
        proof_assert!(i@ == input@.len());
        proof_assert!(input@.subsequence(0, i@) == input@);
        proof_assert!(spec::le(output@.subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@));
        proof_assert!(spec::good_prefix(input@, alpha.decode@, input@.len()));
    }

    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && spec::good_prefix(input@, alpha.decode@, input@.len())
        && 0 <= index@ && index@ <= output@.len()
        && i@ <= index@
        && (forall<k: Int> 0 <= k && k < i@ ==> input@[k] == zero)
        && spec::le(output@.subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@)
        && (forall<k: Int> index@ - i@ <= k && k < index@ ==> output@[k] == 0u8)
        && (index@ == i@ || output@[index@ - i@ - 1] != 0u8)
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(input@.len() - i@))]
    while i < input.len() && input[i] == zero {
        if index >= output.len() {
            #[cfg(creusot)]
            {
                proof_assert!(index@ == output@.len());
                proof_assert!(output@.subsequence(0, index@) == output@);
                creusot_std::prelude::ghost! {
                    let seq = creusot_std::prelude::snapshot!(output@);
                    let n = creusot_std::prelude::snapshot!(index@);
                    lemmas::full_prefix_le(seq, n);
                };
                proof_assert!(spec::le(output@.subsequence(0, index@), 256)
                    == spec::le(output@, 256));
                proof_assert!(lemmas::decode_zero_failure(
                    input@, output@, alpha.encode@, alpha.decode@, i@, output@.len()
                ));
                proof_assert!(!spec::decode_fits(
                    input@, alpha.encode@, alpha.decode@, output@.len()
                ));
            }
            #[cfg(creusot)]
            proof_assert!(spec::decode_error(input@, alpha.encode@, alpha.decode@,
                output@.len(), DecodeError::BufferTooSmall));
            return Err(DecodeError::BufferTooSmall);
        }
        #[cfg(creusot)]
        let before = creusot_std::prelude::snapshot!(output@);
        #[cfg(creusot)]
        let position = creusot_std::prelude::snapshot!(index@);
        output[index] = 0;
        index += 1;
        i += 1;
        #[cfg(creusot)]
        proof_assert!(encoder_lemmas::le_extend(*before, output@, 256, *position));
    }
    #[cfg(creusot)]
    proof_assert!(lemmas::leading_exact(input@, zero, i@, input@.len()));
    #[cfg(creusot)]
    proof_assert!(i@ == spec::leading(input@, zero));
    #[cfg(creusot)]
    let zeros = creusot_std::prelude::snapshot!(i@);
    #[cfg(creusot)]
    proof_assert!(index@ == *zeros || output@[index@ - *zeros - 1] != 0u8);

    #[cfg(creusot)]
    let digits = creusot_std::prelude::snapshot!(output@);
    let mut i = 0;
    let n = index / 2;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= n@ && n@ == index@ / 2
        && 0 <= index@ && index@ <= output@.len()
        && spec::good_prefix(input@, alpha.decode@, input@.len())
        && spec::le((*digits).subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@)
        && *zeros == spec::leading(input@, zero) && 0 <= *zeros && *zeros <= index@
        && (forall<k: Int> index@ - *zeros <= k && k < index@ ==>
            (*digits)[k] == 0u8)
        && (index@ == *zeros || (*digits)[index@ - *zeros - 1] != 0u8)
        && (forall<k: Int> 0 <= k && k < i@ ==>
            output@[k] == (*digits)[index@ - 1 - k])
        && (forall<k: Int> i@ <= k && k < index@ - i@ ==>
            output@[k] == (*digits)[k])
        && (forall<k: Int> index@ - i@ <= k && k < index@ ==>
            output@[k] == (*digits)[index@ - 1 - k])
        && spec::unchanged_suffix(*original, output@, index@)))]
    #[cfg_attr(creusot, variant(n@ - i@))]
    while i < n {
        #[cfg(creusot)]
        proof_assert!(i@ < index@ - 1 - i@);
        #[cfg(creusot)]
        {
            proof_assert!(output@[i@] == (*digits)[i@]);
            proof_assert!(output@[index@ - 1 - i@] == (*digits)[index@ - 1 - i@]);
        }
        let x = output[i];
        output[i] = output[index - 1 - i];
        output[index - 1 - i] = x;
        #[cfg(creusot)]
        {
            proof_assert!(output@[i@] == (*digits)[index@ - 1 - i@]);
            proof_assert!(output@[index@ - 1 - i@] == (*digits)[i@]);
        }
        i += 1;
    }
    #[cfg(creusot)]
    {
        proof_assert!(forall<k: Int> 0 <= k && k < index@ ==>
            output@[k] == (*digits)[index@ - 1 - k]);
        proof_assert!(lemmas::le_reverse_be(*digits, output@, 256, index@));
        proof_assert!(lemmas::leading_reverse(*digits, output@, 0u8, *zeros, index@));
        proof_assert!(lemmas::decode_success_fits(
            input@, *digits, alpha.encode@, alpha.decode@,
            *zeros, index@, output@.len()
        ));
        proof_assert!(spec::be(output@.subsequence(0, index@), 256)
            == spec::le((*digits).subsequence(0, index@), 256));
        proof_assert!(spec::be(output@.subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@));
        proof_assert!(spec::leading(output@.subsequence(0, index@), 0u8) == *zeros);
        proof_assert!(spec::leading(input@, alpha.encode@[0]) == *zeros);
        proof_assert!(spec::decode_fits(input@, alpha.encode@, alpha.decode@, output@.len()));
        proof_assert!(spec::decoded(
            input@, output@.subsequence(0, index@),
            alpha.encode@, alpha.decode@
        ));
    }
    Ok(index)
}

// Publication fixture: expanded non-const verification instance.
// The accepted application workspace retains its native const decoder.
/// Fixed-output variant of `decode_into` from bs58 0.5.1.
#[cfg_attr(creusot, check(terminates))]
#[cfg_attr(creusot, requires(spec::valid_alphabet(alpha.encode@, alpha.decode@)))]
#[cfg_attr(creusot, ensures(spec::decode_const_result(input@, alpha.encode@, alpha.decode@, result)))]
pub fn decode_into_const<const N: usize>(input: &[u8], alpha: &Alphabet) -> Result<[u8; N], DecodeError> {
    let mut output = [0u8; N];
    let mut index = 0;
    let zero = alpha.encode[0];

    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && spec::good_prefix(input@, alpha.decode@, i@)
        && 0 <= index@ && index@ <= N@
        && spec::le(output@.subsequence(0, index@), 256)
            == spec::be58(input@.subsequence(0, i@), alpha.decode@)
        && (index@ == 0 || output@[index@ - 1] != 0u8)
        && (forall<k: Int> index@ <= k && k < N@ ==> output@[k] == 0u8)))]
    #[cfg_attr(creusot, variant(input@.len() - i@))]
    while i < input.len() {
        let c = input[i];
        if c > 127 {
            #[cfg(creusot)]
            {
                proof_assert!(lemmas::le_bound(output@.subsequence(0, index@), 256));
                proof_assert!(lemmas::pow_monotone(256, index@, N@));
            }
            return Err(DecodeError::NonAsciiCharacter { index: i });
        }

        let mut val = alpha.decode[c as usize] as usize;
        if val == 0xFF {
            #[cfg(creusot)]
            {
                proof_assert!(lemmas::le_bound(output@.subsequence(0, index@), 256));
                proof_assert!(lemmas::pow_monotone(256, index@, N@));
            }
            return Err(DecodeError::InvalidCharacter {
                character: c as char,
                index: i,
            });
        }
        #[cfg(creusot)]
        proof_assert!(spec::be58_step(input@, alpha.decode@, i@));
        #[cfg(creusot)]
        let old_digits = output;
        #[cfg(creusot)]
        let old_index = index;

        let mut j = 0;
        #[cfg_attr(creusot, invariant(0 <= i@ && i@ < input@.len()
            && spec::good_prefix(input@, alpha.decode@, i@ + 1)
            && 0 <= j@ && j@ <= index@
            && old_index@ == index@
            && spec::le(old_digits@.subsequence(0, index@), 256)
                == spec::be58(input@.subsequence(0, i@), alpha.decode@)
            && (index@ == 0 || old_digits@[index@ - 1] != 0u8)
            && 0 <= val@ && val@ <= 57
            && 0 <= index@ && index@ <= N@
            && spec::le(output@.subsequence(0, j@), 256)
                + spec::pow(256, j@) * val@
                + 58 * spec::pow(256, j@)
                    * spec::le(output@.subsequence(j@, index@), 256)
                == spec::be58(input@.subsequence(0, i@ + 1), alpha.decode@)
            && (forall<k: Int> index@ <= k && k < N@ ==> output@[k] == 0u8)))]
        #[cfg_attr(creusot, variant(index@ - j@))]
        while j < index {
            #[cfg(creusot)]
            let before = output;
            #[cfg(creusot)]
            let old_carry = val;
            #[cfg(creusot)]
            let position = j;
            let byte = output[j];
            val += (byte as usize) * 58;
            output[j] = (val % 256) as u8;
            val /= 256;
            j += 1;
            #[cfg(creusot)]
            {
                proof_assert!(j@ == position@ + 1);
                proof_assert!(encoder_lemmas::le_extend(before@, output@, 256, position@));
                creusot_std::prelude::ghost! {
                    let old = creusot_std::prelude::snapshot!(before@);
                    let new = creusot_std::prelude::snapshot!(output@);
                    let radix = creusot_std::prelude::snapshot!(256);
                    let old_position = creusot_std::prelude::snapshot!(position@);
                    let new_position = creusot_std::prelude::snapshot!(j@);
                    lemmas::le_extend_step(old, new, radix, old_position, new_position);
                };
                proof_assert!(before@.subsequence(position@, index@).len() == index@ - position@);
                proof_assert!(before@.subsequence(position@, index@)[0] == before@[position@]);
                proof_assert!(old_carry@ + before@[position@]@ * 58
                    == val@ * 256 + output@[position@]@);
                proof_assert!(before@.subsequence(j@, index@)
                    == output@.subsequence(j@, index@));
                proof_assert!(before@.subsequence(position@, index@).subsequence(1, index@ - position@)
                    == output@.subsequence(j@, index@));
                proof_assert!(spec::pow(256, j@) == 256 * spec::pow(256, position@));
                proof_assert!(spec::le(output@.subsequence(0, j@), 256)
                    == spec::le(before@.subsequence(0, position@), 256)
                        + spec::pow(256, position@) * output@[position@]@);
                proof_assert!(spec::le(before@.subsequence(position@, index@), 256)
                    == before@[position@]@
                        + 256 * spec::le(output@.subsequence(j@, index@), 256));
                creusot_std::prelude::ghost! {
                    let a = creusot_std::prelude::snapshot!(spec::le(before@.subsequence(0, position@), 256));
                    let p = creusot_std::prelude::snapshot!(spec::pow(256, position@));
                    let c = creusot_std::prelude::snapshot!(old_carry@);
                    let d = creusot_std::prelude::snapshot!(before@[position@]@);
                    let t = creusot_std::prelude::snapshot!(spec::le(before@.subsequence(position@, index@), 256));
                    let b = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(0, j@), 256));
                    let q = creusot_std::prelude::snapshot!(spec::pow(256, j@));
                    let n = creusot_std::prelude::snapshot!(val@);
                    let e = creusot_std::prelude::snapshot!(output@[position@]@);
                    let u = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(j@, index@), 256));
                    lemmas::decode_horner_step(a, p, c, d, t, b, q, n, e, u);
                };
            }
        }
        #[cfg(creusot)]
        if val == 0 && index > 0 {
            proof_assert!(j@ == index@);
            proof_assert!(spec::le(output@.subsequence(j@, index@), 256) == 0);
            proof_assert!(spec::le(output@.subsequence(0, index@), 256)
                == 58 * spec::le(old_digits@.subsequence(0, index@), 256)
                    + spec::digit(alpha.decode@, c));
            proof_assert!(lemmas::decode_canonical_growth(
                old_digits@, output@, index@,
                spec::digit(alpha.decode@, c)
            ));
            proof_assert!(output@[index@ - 1] != 0u8);
        }

        #[cfg(creusot)]
        {
            proof_assert!(j@ == index@);
            proof_assert!(spec::le(output@.subsequence(j@, index@), 256) == 0);
        }

        #[cfg_attr(creusot, invariant(0 <= i@ && i@ < input@.len()
            && spec::good_prefix(input@, alpha.decode@, i@ + 1)
            && 0 <= index@ && index@ <= N@
            && old_index@ <= index@
            && (val@ > 0 ==> index@ == old_index@)
            && (val@ == 0 ==> (index@ == 0 || output@[index@ - 1] != 0u8))
            && 0 <= val@ && val@ <= 57
            && spec::le(output@.subsequence(0, index@), 256)
                + spec::pow(256, index@) * val@
                == spec::be58(input@.subsequence(0, i@ + 1), alpha.decode@)
            && (forall<k: Int> index@ <= k && k < N@ ==> output@[k] == 0u8)))]
        #[cfg_attr(creusot, variant(val@))]
        while val > 0 {
            if index >= output.len() {
                #[cfg(creusot)]
                proof_assert!(output@.subsequence(0, index@) == output@);
                #[cfg(creusot)]
                proof_assert!(index@ == N@);
                #[cfg(creusot)]
                proof_assert!(spec::le(output@, 256)
                    + spec::pow(256, N@) * val@
                    == spec::be58(input@.subsequence(0, i@ + 1), alpha.decode@));
                #[cfg(creusot)]
                proof_assert!(lemmas::decode_growth_failure(
                    input@, output@, alpha.decode@, i@ + 1, N@, val@
                ));
                #[cfg(creusot)]
                proof_assert!(exists<consumed: Int> consumed == i@ + 1
                    && spec::good_prefix(input@, alpha.decode@, consumed)
                    && spec::be58(input@.subsequence(0, consumed), alpha.decode@)
                        >= spec::pow(256, N@));
                return Err(DecodeError::BufferTooSmall);
            }
            #[cfg(creusot)]
            let before = output;
            #[cfg(creusot)]
            let position = index;
            #[cfg(creusot)]
            let incoming = val;
            output[index] = (val % 256) as u8;
            index += 1;
            val /= 256;
            #[cfg(creusot)]
            {
                proof_assert!(encoder_lemmas::le_extend(before@, output@, 256, position@));
                proof_assert!(spec::pow(256, index@) == 256 * spec::pow(256, position@));
                proof_assert!(output@[position@]@ == incoming@ % 256);
                proof_assert!(val@ == incoming@ / 256);
                creusot_std::prelude::ghost! {
                    let a = creusot_std::prelude::snapshot!(spec::le(before@.subsequence(0, position@), 256));
                    let p = creusot_std::prelude::snapshot!(spec::pow(256, position@));
                    let c = creusot_std::prelude::snapshot!(incoming@);
                    let b = creusot_std::prelude::snapshot!(spec::le(output@.subsequence(0, index@), 256));
                    let q = creusot_std::prelude::snapshot!(spec::pow(256, index@));
                    let n = creusot_std::prelude::snapshot!(val@);
                    let d = creusot_std::prelude::snapshot!(output@[position@]@);
                    lemmas::decode_append_step(a, p, c, b, q, n, d);
                };
            }
        }
        i += 1;
    }

    #[cfg(creusot)]
    {
        proof_assert!(input@.subsequence(0, i@) == input@);
        proof_assert!(spec::good_prefix(input@, alpha.decode@, input@.len()));
    }
    let mut i = 0;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= input@.len()
        && spec::good_prefix(input@, alpha.decode@, input@.len())
        && 0 <= index@ && index@ <= N@
        && i@ <= index@
        && (forall<k: Int> 0 <= k && k < i@ ==> input@[k] == zero)
        && spec::le(output@.subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@)
        && (forall<k: Int> index@ - i@ <= k && k < index@ ==> output@[k] == 0u8)
        && (index@ == i@ || output@[index@ - i@ - 1] != 0u8)
        && (forall<k: Int> index@ <= k && k < N@ ==> output@[k] == 0u8)))]
    #[cfg_attr(creusot, variant(input@.len() - i@))]
    while i < input.len() && input[i] == zero {
        #[cfg(creusot)]
        proof_assert!(forall<k: Int> 0 <= k && k <= i@ ==> input@[k] == zero);
        if index >= output.len() {
            #[cfg(creusot)]
            proof_assert!(output@.subsequence(0, index@) == output@);
            #[cfg(creusot)]
            proof_assert!(index@ == N@);
            #[cfg(creusot)]
            proof_assert!(spec::le(output@, 256) == spec::be58(input@, alpha.decode@));
            #[cfg(creusot)]
            proof_assert!(lemmas::decode_zero_failure(
                input@, output@, alpha.encode@, alpha.decode@, i@, N@
            ));
            #[cfg(creusot)]
            proof_assert!(!spec::decode_fits(input@, alpha.encode@, alpha.decode@, N@));
            #[cfg(creusot)]
            proof_assert!(spec::decode_error(input@, alpha.encode@, alpha.decode@,
                N@, DecodeError::BufferTooSmall));
            return Err(DecodeError::BufferTooSmall);
        }
        #[cfg(creusot)]
        let before = output;
        #[cfg(creusot)]
        let position = index;
        output[index] = 0;
        index += 1;
        i += 1;
        #[cfg(creusot)]
        proof_assert!(encoder_lemmas::le_extend(before@, output@, 256, position@));
    }
    #[cfg(creusot)]
    proof_assert!(lemmas::leading_exact(input@, zero, i@, input@.len()));
    #[cfg(creusot)]
    let zeros = i;

    #[cfg(creusot)]
    let digits = output;
    #[cfg(creusot)]
    {
        proof_assert!(input@.subsequence(0, input@.len()) == input@);
        proof_assert!(zeros@ == spec::leading(input@, zero));
    }
    let mut i = 0;
    let n = index / 2;
    #[cfg_attr(creusot, invariant(0 <= i@ && i@ <= n@ && n@ == index@ / 2
        && 0 <= index@ && index@ <= N@
        && spec::good_prefix(input@, alpha.decode@, input@.len())
        && spec::le(digits@.subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@)
        && zeros@ == spec::leading(input@, zero) && 0 <= zeros@ && zeros@ <= index@
        && (forall<k: Int> index@ - zeros@ <= k && k < index@ ==>
            digits@[k] == 0u8)
        && (index@ == zeros@ || digits@[index@ - zeros@ - 1] != 0u8)
        && (forall<k: Int> 0 <= k && k < i@ ==>
            output@[k] == digits@[index@ - 1 - k])
        && (forall<k: Int> i@ <= k && k < index@ - i@ ==>
            output@[k] == digits@[k])
        && (forall<k: Int> index@ - i@ <= k && k < index@ ==>
            output@[k] == digits@[index@ - 1 - k])
        && (forall<k: Int> index@ <= k && k < N@ ==> output@[k] == 0u8)))]
    #[cfg_attr(creusot, variant(n@ - i@))]
    while i < n {
        #[cfg(creusot)]
        proof_assert!(i@ < index@ - 1 - i@);
        #[cfg(creusot)]
        {
            proof_assert!(output@[i@] == digits@[i@]);
            proof_assert!(output@[index@ - 1 - i@] == digits@[index@ - 1 - i@]);
        }
        let x = output[i];
        output[i] = output[index - 1 - i];
        output[index - 1 - i] = x;
        #[cfg(creusot)]
        {
            proof_assert!(output@[i@] == digits@[index@ - 1 - i@]);
            proof_assert!(output@[index@ - 1 - i@] == digits@[i@]);
        }
        i += 1;
    }
    #[cfg(creusot)]
    {
        proof_assert!(forall<k: Int> 0 <= k && k < index@ ==>
            output@[k] == digits@[index@ - 1 - k]);
        proof_assert!(lemmas::le_reverse_be(digits@, output@, 256, index@));
        proof_assert!(lemmas::leading_reverse(digits@, output@, 0u8, zeros@, index@));
        proof_assert!(spec::be(output@.subsequence(0, index@), 256)
            == spec::be58(input@, alpha.decode@));
        proof_assert!(spec::leading(output@.subsequence(0, index@), 0u8) == zeros@);
        proof_assert!(lemmas::decode_success_fits(
            input@, digits@, alpha.encode@, alpha.decode@,
            zeros@, index@, N@
        ));
        proof_assert!(spec::decoded(
            input@, output@.subsequence(0, index@),
            alpha.encode@, alpha.decode@
        ));
        proof_assert!(exists<used: Int> used == index@
            && 0 <= used && used <= N@
            && spec::decoded(input@, output@.subsequence(0, used),
                alpha.encode@, alpha.decode@)
            && (forall<k: Int> used <= k && k < N@ ==> output@[k] == 0u8));
    }

    Ok(output)
}
pub mod wrappers;

#[cfg(creusot)]
pub mod roundtrip;

pub mod defaults;

// The release derives Clone for these Copy enums. Explicit copying avoids the
// stock char::clone boundary, which has no exact-value postcondition in 0.13.
#[cfg(creusot)]
impl Clone for AlphabetError {
    #[ensures(result == *self)]
    fn clone(&self) -> Self { *self }
}
#[cfg(creusot)]
impl Clone for EncodeError {
    #[ensures(result == *self)]
    fn clone(&self) -> Self { *self }
}
#[cfg(creusot)]
impl Clone for DecodeError {
    #[ensures(result == *self)]
    fn clone(&self) -> Self { *self }
}

pub mod checked_state;
