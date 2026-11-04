//! State-only projection with both release checksum features enabled.
//! No codec methods or digest computations are part of this projection.
use crate::Alphabet;
#[cfg(creusot)]
use creusot_std::prelude::*;

pub enum Check { Disabled, Enabled(Option<u8>), CB58(Option<u8>) }

pub struct EncodeBuilder<'a, I: AsRef<[u8]>> { pub input: I, pub alpha: &'a Alphabet, pub check: Check }
impl<'a, I: AsRef<[u8]>> EncodeBuilder<'a, I> {
    #[cfg_attr(creusot, ensures(result.input == input && result.alpha == alpha && result.check == Check::Disabled))]
    pub fn new(input: I, alpha: &'a Alphabet) -> EncodeBuilder<'a, I> {
        EncodeBuilder { input, alpha, check: Check::Disabled }
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == alpha && result.check == self.check))]
    pub fn with_alphabet(self, alpha: &'a Alphabet) -> EncodeBuilder<'a, I> {
        EncodeBuilder { alpha, ..self }
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == self.alpha && result.check == Check::Enabled(None)))]
    pub fn with_check(self) -> EncodeBuilder<'a, I> {
        let check = Check::Enabled(None);
        EncodeBuilder { check, ..self }
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == self.alpha && result.check == Check::Enabled(Some(expected_ver))))]
    pub fn with_check_version(self, expected_ver: u8) -> EncodeBuilder<'a, I> {
        let check = Check::Enabled(Some(expected_ver));
        EncodeBuilder { check, ..self }
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == self.alpha && result.check == Check::CB58(expected_ver)))]
    pub fn as_cb58(self, expected_ver: Option<u8>) -> EncodeBuilder<'a, I> {
        let check = Check::CB58(expected_ver);
        EncodeBuilder { check, ..self }
    }
}

pub struct DecodeBuilder<'a, I: AsRef<[u8]>> { pub input: I, pub alpha: &'a Alphabet, pub check: Check }
impl<'a, I: AsRef<[u8]>> DecodeBuilder<'a, I> {
    #[cfg_attr(creusot, ensures(result.input == input && result.alpha == alpha && result.check == Check::Disabled))]
    pub const fn new(input: I, alpha: &'a Alphabet) -> DecodeBuilder<'a, I> {
        DecodeBuilder { input, alpha, check: Check::Disabled }
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == alpha && result.check == self.check))]
    pub const fn with_alphabet(mut self, alpha: &'a Alphabet) -> DecodeBuilder<'a, I> {
        self.alpha = alpha;
        self
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == self.alpha && result.check == Check::Enabled(expected_ver)))]
    pub fn with_check(self, expected_ver: Option<u8>) -> DecodeBuilder<'a, I> {
        let check = Check::Enabled(expected_ver);
        DecodeBuilder { check, ..self }
    }
    #[cfg_attr(creusot, ensures(result.input == self.input && result.alpha == self.alpha && result.check == Check::CB58(expected_ver)))]
    pub fn as_cb58(self, expected_ver: Option<u8>) -> DecodeBuilder<'a, I> {
        let check = Check::CB58(expected_ver);
        DecodeBuilder { check, ..self }
    }
}

