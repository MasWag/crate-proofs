// Required methods retain their release signatures; unused supertraits are omitted.
pub use lexical_util::result::Result;

pub trait FromLexical: Sized {
    fn from_lexical(bytes: &[u8]) -> Result<Self>;
    fn from_lexical_partial(bytes: &[u8]) -> Result<(Self, usize)>;
}

pub trait FromLexicalWithOptions: Sized {
    type Options;
    fn from_lexical_with_options<const FORMAT: u128>(bytes: &[u8], options: &Self::Options) -> Result<Self>;
    fn from_lexical_partial_with_options<const FORMAT: u128>(bytes: &[u8], options: &Self::Options) -> Result<(Self, usize)>;
}

pub trait ToLexical: Sized {
    fn to_lexical<'a>(self, bytes: &'a mut [u8]) -> &'a mut [u8];
}

pub trait ToLexicalWithOptions: Sized {
    type Options;
    fn to_lexical_with_options<'a, const FORMAT: u128>(self, bytes: &'a mut [u8], options: &Self::Options) -> &'a mut [u8];
}


pub fn write<N: ToLexical>(n: N, bytes: &mut [u8]) -> &mut [u8] {
    n.to_lexical(bytes)
}

pub fn write_with_options<'a, N: ToLexicalWithOptions, const FORMAT: u128>(
    n: N,
    bytes: &'a mut [u8],
    options: &N::Options,
) -> &'a mut [u8] {
    n.to_lexical_with_options::<FORMAT>(bytes, options)
}

pub fn parse<N: FromLexical>(bytes: &[u8]) -> Result<N> {
    N::from_lexical(bytes)
}

pub fn parse_partial<N: FromLexical>(bytes: &[u8]) -> Result<(N, usize)> {
    N::from_lexical_partial(bytes)
}

pub fn parse_with_options<N: FromLexicalWithOptions, const FORMAT: u128>(
    bytes: &[u8],
    options: &N::Options,
) -> Result<N> {
    N::from_lexical_with_options::<FORMAT>(bytes, options)
}

pub fn parse_partial_with_options<N: FromLexicalWithOptions, const FORMAT: u128>(
    bytes: &[u8],
    options: &N::Options,
) -> Result<(N, usize)> {
    N::from_lexical_partial_with_options::<FORMAT>(bytes, options)
}
