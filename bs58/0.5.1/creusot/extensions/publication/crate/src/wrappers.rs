//! Checked, no-checksum public API specializations and release target adapters.
use crate::{Alphabet, EncodeError, DecodeError, encode_into, decode_into};
#[cfg(creusot)]
use creusot_std::prelude::*;

pub trait TargetModel {
    #[cfg(creusot)]
    #[logic]
    fn bytes(self) -> Seq<u8>;
}
impl TargetModel for [u8] {
    #[cfg(creusot)]
    #[logic(open)]
    fn bytes(self) -> Seq<u8> { pearlite! { self@ } }
}
impl<const N: usize> TargetModel for [u8; N] {
    #[cfg(creusot)]
    #[logic(open)]
    fn bytes(self) -> Seq<u8> { pearlite! { self@ } }
}
impl<T: TargetModel + ?Sized> TargetModel for &mut T {
    #[cfg(creusot)]
    #[logic(open)]
    fn bytes(self) -> Seq<u8> { pearlite! { (*self).bytes() } }
}

pub trait EncodeTarget: TargetModel {
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn encode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, EncodeError>) -> Result<usize, EncodeError>;
}
impl EncodeTarget for [u8] {
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn encode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, EncodeError>) -> Result<usize, EncodeError> {
        let _ = max_len;
        f(&mut *self)
    }
}

pub enum Check { Disabled }

pub struct EncodeBuilder<'a, I: AsRef<[u8]>> { pub input: I, pub alpha: &'a Alphabet, check: Check }
impl<'a, I: AsRef<[u8]>> EncodeBuilder<'a, I> {
    #[cfg_attr(creusot, ensures(result.input == input && result.alpha == alpha))]
    pub fn new(input: I, alpha: &'a Alphabet) -> Self { Self { input, alpha, check: Check::Disabled } }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == alpha))]
    pub fn with_alphabet(self, alpha: &'a Alphabet) -> Self { Self { alpha, ..self } }
}
impl<'a, 'b> EncodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, requires(self.input@.len() + (self.input@.len() + 1) / 2 <= usize::MAX@))]
    #[cfg_attr(creusot, ensures(crate::spec::encode_result(self.input@, output@, (^output)@,
        self.alpha.encode@, self.alpha.decode@, result)))]
    pub fn onto(self, mut output: &mut [u8]) -> Result<usize, EncodeError> {
        let input = self.input.as_ref();
        match self.check {
            Check::Disabled => EncodeTarget::encode_with(&mut output, max_encoded_len(input.len()), |output| encode_into(input, output, self.alpha)),
        }
    }
}
#[cfg_attr(creusot, requires(len@ + (len@ + 1) / 2 <= usize::MAX@))]
#[cfg_attr(creusot, ensures(result@ == len@ + (len@ + 1) / 2))]
pub fn max_encoded_len(len: usize) -> usize { len + (len + 1) / 2 }

pub trait DecodeTarget: TargetModel {
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn decode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, DecodeError>) -> Result<usize, DecodeError>;
}
impl DecodeTarget for [u8] {
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn decode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, DecodeError>) -> Result<usize, DecodeError> {
        let _ = max_len;
        f(&mut *self)
    }
}
impl<const N: usize> DecodeTarget for [u8; N] {
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn decode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, DecodeError>) -> Result<usize, DecodeError> {
        let _ = max_len;
        f(&mut *self)
    }
}

pub struct DecodeBuilder<'a, I: AsRef<[u8]>> { pub input: I, pub alpha: &'a Alphabet, check: Check }
impl<'a, I: AsRef<[u8]>> DecodeBuilder<'a, I> {
    #[cfg_attr(creusot, ensures(result.input == input && result.alpha == alpha))]
    pub const fn new(input: I, alpha: &'a Alphabet) -> Self { Self { input, alpha, check: Check::Disabled } }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == alpha))]
    pub fn with_alphabet(self, alpha: &'a Alphabet) -> Self { Self { alpha, ..self } }
}
impl<'a, 'b> DecodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, ensures(crate::spec::decode_result(self.input@, output@, (^output)@,
        self.alpha.encode@, self.alpha.decode@, result)))]
    pub fn onto(self, mut output: &mut [u8]) -> Result<usize, DecodeError> {
        let max_decoded_len = self.input.as_ref().len();
        match self.check {
            Check::Disabled => DecodeTarget::decode_with(&mut output, max_decoded_len, |output| decode_into(self.input.as_ref(), output, self.alpha)),
        }
    }
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, ensures(crate::spec::decode_result(self.input@, output@, (^output)@,
        self.alpha.encode@, self.alpha.decode@, result)))]
    pub fn onto_array<const N: usize>(self, mut output: &mut [u8; N]) -> Result<usize, DecodeError> {
        let max_decoded_len = self.input.as_ref().len();
        match self.check {
            Check::Disabled => DecodeTarget::decode_with(&mut output, max_decoded_len, |output| decode_into(self.input.as_ref(), output, self.alpha)),
        }
    }
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, ensures(crate::spec::decode_const_result(self.input@, self.alpha.encode@, self.alpha.decode@, result)))]
    pub fn into_array_const<const N: usize>(self) -> Result<[u8; N], DecodeError> {
        assert!(matches!(self.check, Check::Disabled), "checksums in const aren't supported (why are you using this API at runtime)");
        crate::decode_into_const(self.input, self.alpha)
    }
}

impl<T: EncodeTarget + ?Sized> EncodeTarget for &mut T {
    #[cfg_attr(creusot, ensures(^(^self) == ^*self))]
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn encode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, EncodeError>) -> Result<usize, EncodeError> {
        T::encode_with(self, max_len, f)
    }
}
impl<T: DecodeTarget + ?Sized> DecodeTarget for &mut T {
    #[cfg_attr(creusot, ensures(^(^self) == ^*self))]
    #[cfg_attr(creusot, requires(forall<b: &mut [u8]> b@ == self.bytes() ==> f.precondition((b,))))]
    #[cfg_attr(creusot, ensures(exists<b: &mut [u8]> b@ == self.bytes() && (^b)@ == (^self).bytes() && f.postcondition_once((b,), result)))]
    fn decode_with(&mut self, max_len: usize,
        f: impl for<'a> FnOnce(&'a mut [u8]) -> Result<usize, DecodeError>) -> Result<usize, DecodeError> {
        T::decode_with(self, max_len, f)
    }
}

impl<'a, 'b> EncodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, requires(self.input@.len() + (self.input@.len() + 1) / 2 <= usize::MAX@))]
    #[cfg_attr(creusot, requires(output@.len() + self.input@.len() + (self.input@.len() + 1) / 2 <= usize::MAX@))]
    #[cfg_attr(creusot, ensures(forall<i: Int> 0 <= i && i < output@.len() ==> (^output)@[i] == output@[i]))]
    #[cfg_attr(creusot, ensures(match result {
        Ok(n) => (^output)@.len() == output@.len() + n@
            && crate::spec::encoded(self.input@, (^output)@.subsequence(output@.len(), (^output)@.len()), self.alpha.encode@, self.alpha.decode@),
        Err(EncodeError::BufferTooSmall) => (^output)@.len() == output@.len() + self.input@.len() + (self.input@.len() + 1) / 2
            && !crate::spec::encode_fits(self.input@, self.input@.len() + (self.input@.len() + 1) / 2),
    }))]
    #[cfg_attr(creusot, ensures(match result { Ok(_) => true, Err(_) => false }))]
    pub fn onto_vec(self, output: &mut alloc::vec::Vec<u8>) -> Result<usize, EncodeError> {
        #[cfg(creusot)]
        proof_assert!(crate::roundtrip::encode_capacity(self.input@));
        let original = output.len();
        let max_len = max_encoded_len(self.input.len());
        crate::vec_utils::grow_zero(output, original + max_len);
        let len = match encode_into(self.input, &mut output[original..], self.alpha) { Ok(n) => n, Err(e) => return Err(e) };
        #[cfg(creusot)]
        let tail = snapshot!(output@.subsequence(original@, output@.len()).subsequence(0, len@));
        crate::vec_utils::truncate(output, original + len);
        #[cfg(creusot)]
        proof_assert!(output@.subsequence(original@, output@.len()) == *tail);
        Ok(len)
    }
}
impl<'a, 'b> DecodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, requires(output@.len() + self.input@.len() <= usize::MAX@))]
    #[cfg_attr(creusot, ensures(forall<i: Int> 0 <= i && i < output@.len() ==> (^output)@[i] == output@[i]))]
    #[cfg_attr(creusot, ensures(match result {
        Ok(n) => (^output)@.len() == output@.len() + n@
            && crate::spec::decoded(self.input@, (^output)@.subsequence(output@.len(), (^output)@.len()), self.alpha.encode@, self.alpha.decode@),
        Err(error) => (^output)@.len() == output@.len() + self.input@.len()
            && crate::spec::decode_error(self.input@, self.alpha.encode@, self.alpha.decode@, self.input@.len(), error),
    }))]
    #[cfg_attr(creusot, ensures(crate::spec::good_prefix(self.input@, self.alpha.decode@, self.input@.len()) ==>
        match result { Ok(_) => true, Err(_) => false }))]
    #[cfg_attr(creusot, ensures(match result { Err(DecodeError::BufferTooSmall) => false, _ => true }))]
    pub fn onto_vec(self, output: &mut alloc::vec::Vec<u8>) -> Result<usize, DecodeError> {
        let original = output.len();
        let max_len = self.input.len();
        crate::vec_utils::grow_zero(output, original + max_len);
        let len = match decode_into(self.input, &mut output[original..], self.alpha) {
            Ok(n) => n,
            Err(e) => {
                #[cfg(creusot)]
                proof_assert!(crate::roundtrip::decode_no_buffer_error(self.input@, self.alpha.encode@, self.alpha.decode@));
                #[cfg(creusot)]
                proof_assert!(crate::spec::good_prefix(self.input@, self.alpha.decode@, self.input@.len()) ==>
                    crate::roundtrip::decode_capacity(self.input@, self.alpha.encode@, self.alpha.decode@)
                    && crate::roundtrip::decode_error_excluded(self.input@, self.alpha.encode@, self.alpha.decode@, self.input@.len(), e));
                return Err(e)
            },
        };
        #[cfg(creusot)]
        let tail = snapshot!(output@.subsequence(original@, output@.len()).subsequence(0, len@));
        crate::vec_utils::truncate(output, original + len);
        #[cfg(creusot)]
        proof_assert!(output@.subsequence(original@, output@.len()) == *tail);
        Ok(len)
    }
}

impl<'a, 'b> DecodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, requires(crate::spec::decode_fits(self.input@, self.alpha.encode@, self.alpha.decode@, N@)))]
    #[cfg_attr(creusot, ensures(crate::spec::decode_const_result(self.input@, self.alpha.encode@, self.alpha.decode@, Ok(result))))]
    pub fn into_array_const_unwrap<const N: usize>(self) -> [u8; N] {
        #[cfg(creusot)]
        let input = self.input;
        #[cfg(creusot)]
        let alpha = self.alpha;
        match self.into_array_const() {
            Ok(result) => result,
            Err(DecodeError::BufferTooSmall) => {
                #[cfg(creusot)]
                proof_assert!(crate::roundtrip::decode_error_excluded(input@, alpha.encode@, alpha.decode@, N@, DecodeError::BufferTooSmall));
                panic!("buffer provided to decode base58 encoded string into was too small")
            },
            Err(e) => {
                #[cfg(creusot)]
                proof_assert!(crate::roundtrip::decode_error_excluded(input@, alpha.encode@, alpha.decode@, N@, e));
                match e {
                    DecodeError::InvalidCharacter { .. } => panic!("provided string contained invalid character"),
                    DecodeError::NonAsciiCharacter { .. } => panic!("provided string contained non-ascii character"),
                    DecodeError::BufferTooSmall => panic!("buffer provided to decode base58 encoded string into was too small"),
                }
            },
        }
    }
}

impl Alphabet {
    #[cfg_attr(creusot, requires(crate::spec::valid_base(base@, 58)))]
    #[cfg_attr(creusot, ensures(result.encode@ == base@ && crate::spec::valid_alphabet(result.encode@, result.decode@)))]
    pub const fn new_unwrap(base: &[u8; 58]) -> Self {
        let result = Self::new(base);
        #[allow(unconditional_panic)]
        [][match result {
            Ok(alphabet) => return alphabet,
            Err(_) => 0,
        }]
    }
}

#[cfg(creusot)]
impl Clone for Alphabet {
    #[ensures(result == *self)]
    fn clone(&self) -> Self { Self { encode: self.encode, decode: self.decode } }
}
#[cfg(creusot)]
impl Copy for Alphabet {}

impl<'a, 'b> EncodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, requires(self.input@.len() + (self.input@.len() + 1) / 2 <= usize::MAX@))]
    #[cfg_attr(creusot, ensures(crate::spec::encoded(self.input@, result@, self.alpha.encode@, self.alpha.decode@)))]
    pub fn into_vec(self) -> alloc::vec::Vec<u8> {
        #[cfg(creusot)]
        proof_assert!(crate::roundtrip::encode_capacity(self.input@));
        let mut output = alloc::vec::Vec::new();
        match self.onto_vec(&mut output) {
            Ok(_) => {
                #[cfg(creusot)]
                proof_assert!(output@.subsequence(0, output@.len()) == output@);
                output
            },
            Err(_) => panic!("called `Result::unwrap()` on an `Err` value: BufferTooSmall"),
        }
    }
}
impl<'a, 'b> DecodeBuilder<'a, &'b [u8]> {
    #[cfg_attr(creusot, requires(crate::spec::valid_alphabet(self.alpha.encode@, self.alpha.decode@)))]
    #[cfg_attr(creusot, ensures(match result {
        Ok(v) => crate::spec::decoded(self.input@, v@, self.alpha.encode@, self.alpha.decode@),
        Err(e) => crate::spec::decode_error(self.input@, self.alpha.encode@, self.alpha.decode@, self.input@.len(), e),
    }))]
    #[cfg_attr(creusot, ensures(crate::spec::good_prefix(self.input@, self.alpha.decode@, self.input@.len()) ==>
        match result { Ok(_) => true, Err(_) => false }))]
    #[cfg_attr(creusot, ensures(match result { Err(DecodeError::BufferTooSmall) => false, _ => true }))]
    pub fn into_vec(self) -> Result<alloc::vec::Vec<u8>, DecodeError> {
        let mut output = alloc::vec::Vec::new();
        match self.onto_vec(&mut output) {
            Ok(_) => {
                #[cfg(creusot)]
                proof_assert!(output@.subsequence(0, output@.len()) == output@);
                Ok(output)
            },
            Err(e) => Err(e),
        }
    }
}

/// Concrete client composing both checked codec implementations.
#[cfg_attr(creusot, requires(crate::spec::valid_alphabet(alpha.encode@, alpha.decode@)))]
#[cfg_attr(creusot, requires(input@.len() + (input@.len() + 1) / 2 <= usize::MAX@))]
#[cfg_attr(creusot, ensures(result@ == input@))]
pub fn encode_decode_roundtrip(input: &[u8], alpha: &Alphabet) -> alloc::vec::Vec<u8> {
    #[cfg(creusot)]
    proof_assert!(crate::roundtrip::encode_capacity(input@));
    let text = EncodeBuilder::new(input, alpha).into_vec();
    #[cfg(creusot)]
    proof_assert!(crate::roundtrip::decode_capacity(text@, alpha.encode@, alpha.decode@));
    match DecodeBuilder::new(&text[..], alpha).into_vec() {
        Ok(output) => {
            #[cfg(creusot)]
            proof_assert!(crate::roundtrip::decode_encode(input@, text@, output@, alpha.encode@, alpha.decode@));
            output
        },
        Err(e) => {
            #[cfg(creusot)]
            proof_assert!(crate::roundtrip::decode_error_excluded(text@, alpha.encode@, alpha.decode@, text@.len(), e));
            panic!("codec roundtrip decoding failed")
        }
    }
}
