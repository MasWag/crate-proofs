//! Literal built-in alphabets and default public entry points.
use crate::{Alphabet, wrappers::{EncodeBuilder, DecodeBuilder}};
#[cfg(creusot)]
use creusot_std::prelude::*;

impl Alphabet {
    pub const BITCOIN: &'static Self = &Self::new_unwrap(&[49,50,51,52,53,54,55,56,57,65,66,67,68,69,70,71,72,74,75,76,77,78,80,81,82,83,84,85,86,87,88,89,90,97,98,99,100,101,102,103,104,105,106,107,109,110,111,112,113,114,115,116,117,118,119,120,121,122]);
    pub const MONERO: &'static Self = &Self::new_unwrap(&[49,50,51,52,53,54,55,56,57,65,66,67,68,69,70,71,72,74,75,76,77,78,80,81,82,83,84,85,86,87,88,89,90,97,98,99,100,101,102,103,104,105,106,107,109,110,111,112,113,114,115,116,117,118,119,120,121,122]);
    pub const RIPPLE: &'static Self = &Self::new_unwrap(&[114,112,115,104,110,97,102,51,57,119,66,85,68,78,69,71,72,74,75,76,77,52,80,81,82,83,84,55,86,87,88,89,90,50,98,99,100,101,67,103,54,53,106,107,109,56,111,70,113,105,49,116,117,118,65,120,121,122]);
    pub const FLICKR: &'static Self = &Self::new_unwrap(&[49,50,51,52,53,54,55,56,57,97,98,99,100,101,102,103,104,105,106,107,109,110,111,112,113,114,115,116,117,118,119,120,121,122,65,66,67,68,69,70,71,72,74,75,76,77,78,80,81,82,83,84,85,86,87,88,89,90]);
    pub const DEFAULT: &'static Self = Self::BITCOIN;

    #[cfg_attr(creusot, ensures(crate::spec::valid_alphabet(result.encode@, result.decode@)))]
    pub fn bitcoin() -> Self {
        Self::new_unwrap(&[49,50,51,52,53,54,55,56,57,65,66,67,68,69,70,71,72,74,75,76,77,78,80,81,82,83,84,85,86,87,88,89,90,97,98,99,100,101,102,103,104,105,106,107,109,110,111,112,113,114,115,116,117,118,119,120,121,122])
    }
}

#[cfg_attr(creusot, ensures(result.input == input && result.alpha == Alphabet::DEFAULT))]
#[cfg_attr(creusot, ensures(crate::spec::valid_alphabet(result.alpha.encode@, result.alpha.decode@)))]
pub fn encode<I: AsRef<[u8]>>(input: I) -> EncodeBuilder<'static, I> {
    EncodeBuilder::from_input(input)
}

#[cfg_attr(creusot, ensures(result.input == input && result.alpha == Alphabet::DEFAULT))]
#[cfg_attr(creusot, ensures(crate::spec::valid_alphabet(result.alpha.encode@, result.alpha.decode@)))]
pub fn decode<I: AsRef<[u8]>>(input: I) -> DecodeBuilder<'static, I> {
    DecodeBuilder::from_input(input)
}

// The release's private from_input functions construct these same fields.
// Delegate to the checked constructor so private Check representation stays local.
impl<I: AsRef<[u8]>> EncodeBuilder<'static, I> {
    #[cfg_attr(creusot, ensures(result.input == input && result.alpha == Alphabet::DEFAULT))]
    #[cfg_attr(creusot, ensures(crate::spec::valid_alphabet(result.alpha.encode@, result.alpha.decode@)))]
    pub(crate) fn from_input(input: I) -> Self { Self::new(input, Alphabet::DEFAULT) }
}
impl<I: AsRef<[u8]>> DecodeBuilder<'static, I> {
    #[cfg_attr(creusot, ensures(result.input == input && result.alpha == Alphabet::DEFAULT))]
    #[cfg_attr(creusot, ensures(crate::spec::valid_alphabet(result.alpha.encode@, result.alpha.decode@)))]
    pub(crate) fn from_input(input: I) -> Self { Self::new(input, Alphabet::DEFAULT) }
}
