use bs58_creusot_extensions as fork;
use bs58_upstream as upstream;
use fork::wrappers::{DecodeBuilder, EncodeBuilder};
use std::cell::Cell;

const CONST_ALPHA: fork::Alphabet = fork::Alphabet::new_unwrap(
    b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz");

fn same<T: std::fmt::Debug, U: std::fmt::Debug>(a: T, b: U) {
    assert_eq!(format!("{a:?}"), format!("{b:?}"));
}

fn next(seed: &mut u64) -> u8 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed as u8
}

fn array_cases<const N: usize>(input: &[u8], base: &[u8; 58]) -> usize {
    let original = upstream::Alphabet::new(base).unwrap();
    let adapted = fork::Alphabet::new(base).unwrap();
    let mut left = [0xa5; N];
    let mut right = left;
    same(upstream::decode(input).with_alphabet(&original).onto(&mut left),
         DecodeBuilder::new(input, &adapted).onto_array(&mut right));
    assert_eq!(left, right, "array post-state, capacity {N}, input {input:?}");
    same(upstream::decode(input).with_alphabet(&original).into_array_const::<N>(),
         DecodeBuilder::new(input, &adapted).into_array_const::<N>());
    if upstream::decode(input).with_alphabet(&original).into_array_const::<N>().is_ok() {
        assert_eq!(upstream::decode(input).with_alphabet(&original).into_array_const_unwrap::<N>(),
                   DecodeBuilder::new(input, &adapted).into_array_const_unwrap::<N>());
        return 3;
    }
    2
}

fn wrapper_cases() -> (usize, usize, usize) {
    let mut bases = vec![
        *b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz",
        *b"123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ",
    ];
    let mut controls = [0; 58];
    for (i, b) in controls.iter_mut().enumerate() { *b = i as u8; }
    bases.push(controls);
    let mut seed = 0x0580_051e_2026u64;
    let mut slices = 0;
    let mut arrays = 0;
    let mut vectors = 0;
    for base in bases {
        let original = upstream::Alphabet::new(&base).unwrap();
        let adapted = fork::Alphabet::new(&base).unwrap();
        let default = fork::Alphabet::new(
            b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz").unwrap();
        for iteration in 0..1200 {
            let len = next(&mut seed) as usize % 49;
            let mut input = vec![0; len];
            for byte in &mut input { *byte = next(&mut seed); }
            if iteration % 3 == 0 {
                input[..len.min(iteration % 13)].fill(0);
            }
            let encoded = upstream::encode(&input).with_alphabet(&original).into_vec();
            assert_eq!(fork::wrappers::encode_decode_roundtrip(&input, &adapted), input);
            for candidate in [&input[..], &encoded[..]] {
                let mut capacities = vec![0, 1, len, encoded.len(), len + 8, encoded.len() + 8];
                capacities.sort_unstable(); capacities.dedup();
                for capacity in capacities {
                    let mut left = vec![0xa5; capacity];
                    let mut right = left.clone();
                    same(upstream::encode(candidate).with_alphabet(&original).onto(&mut left[..]),
                         EncodeBuilder::new(candidate, &default).with_alphabet(&adapted).onto(&mut right));
                    assert_eq!(left, right, "encode wrapper full post-state");
                    left.fill(0xa5); right.fill(0xa5);
                    same(upstream::decode(candidate).with_alphabet(&original).onto(&mut left[..]),
                         DecodeBuilder::new(candidate, &default).with_alphabet(&adapted).onto(&mut right));
                    assert_eq!(left, right, "decode wrapper full post-state");
                    slices += 2;
                }
                arrays += array_cases::<0>(candidate, &base);
                arrays += array_cases::<1>(candidate, &base);
                arrays += array_cases::<8>(candidate, &base);
                arrays += array_cases::<64>(candidate, &base);
                arrays += array_cases::<96>(candidate, &base);
                for prefix in [&[][..], &[0xa5, 0, 255][..]] {
                    let mut left = prefix.to_vec();
                    let mut right = left.clone();
                    same(upstream::encode(candidate).with_alphabet(&original).onto(&mut left),
                         EncodeBuilder::new(candidate, &adapted).onto_vec(&mut right));
                    assert_eq!(left, right, "Vec encode complete success/error state");
                    left = prefix.to_vec(); right = left.clone();
                    same(upstream::decode(candidate).with_alphabet(&original).onto(&mut left),
                         DecodeBuilder::new(candidate, &adapted).onto_vec(&mut right));
                    assert_eq!(left, right, "Vec decode complete success/error state");
                    vectors += 2;
                }
                assert_eq!(upstream::encode(candidate).with_alphabet(&original).into_vec(),
                           EncodeBuilder::new(candidate, &adapted).into_vec());
                same(upstream::decode(candidate).with_alphabet(&original).into_vec(),
                     DecodeBuilder::new(candidate, &adapted).into_vec());
                vectors += 2;
            }
        }
    }
    for len in [0, 1, 2, 3, 57, 58, 1000, usize::MAX / 3, (usize::MAX / 3) * 2] {
        let expected = len as u128 + (len as u128 + 1) / 2;
        assert_eq!(fork::wrappers::max_encoded_len(len) as u128, expected);
    }
    (slices, arrays, vectors)
}

// These are semantic-boundary witnesses, not application bugs or formal proofs.
fn generic_boundary_witnesses() {
    struct Skip;
    impl upstream::encode::EncodeTarget for Skip {
        fn encode_with(&mut self, _: usize,
            _: impl for<'a> FnOnce(&'a mut [u8]) -> upstream::encode::Result<usize>
        ) -> upstream::encode::Result<usize> { Ok(0) }
    }
    assert_eq!(upstream::encode([1]).onto(Skip), Ok(0));

    struct Changing(Cell<usize>);
    impl AsRef<[u8]> for Changing {
        fn as_ref(&self) -> &[u8] {
            let n = self.0.get(); self.0.set(n + 1);
            if n == 0 { b"2" } else { b"zzzzzzzz" }
        }
    }
    assert!(upstream::decode(b"zzzzzzzz").into_vec().is_ok());
    let changing = Changing(Cell::new(0));
    assert_eq!(upstream::decode(&changing).into_vec(),
               Err(upstream::decode::Error::BufferTooSmall));
    assert_eq!(changing.0.get(), 2);

    let mut text = String::from("retained prefix");
    let result = upstream::encode::EncodeTarget::encode_with(&mut text, 1,
        |_| Err(upstream::encode::Error::BufferTooSmall));
    assert_eq!(result, Err(upstream::encode::Error::BufferTooSmall));
    assert!(text.is_empty());
    println!("boundary_witnesses: 3 (custom target, repeated AsRef, String error state); not bugs");
}

fn default_cases() {
    let builtins = [
        (fork::Alphabet::BITCOIN, upstream::Alphabet::BITCOIN),
        (fork::Alphabet::MONERO, upstream::Alphabet::MONERO),
        (fork::Alphabet::RIPPLE, upstream::Alphabet::RIPPLE),
        (fork::Alphabet::FLICKR, upstream::Alphabet::FLICKR),
        (fork::Alphabet::DEFAULT, upstream::Alphabet::DEFAULT),
    ];
    for (adapted, original) in builtins {
        for byte in 0u8..=255 {
            let input = [0, byte, 255];
            let expected = upstream::encode(input).with_alphabet(original).into_vec();
            assert_eq!(EncodeBuilder::new(&input[..], adapted).into_vec(), expected);
            same(upstream::decode(&expected).with_alphabet(original).into_vec(),
                 DecodeBuilder::new(&expected[..], adapted).into_vec());
        }
    }
    assert_eq!(fork::Alphabet::MONERO.encode, fork::Alphabet::BITCOIN.encode);
    assert_eq!(fork::Alphabet::DEFAULT.encode, fork::Alphabet::BITCOIN.encode);
    for byte in 0u8..=255 {
        let input = [0, byte, 255];
        let text = upstream::encode(input).into_vec();
        assert_eq!(fork::defaults::encode(&input[..]).into_vec(), text);
        same(upstream::decode(&text).into_vec(), fork::defaults::decode(&text[..]).into_vec());
    }
    println!("extension_defaults: builtin_codec_cases=2560; frontend_cases=512; constant_alias_values=true");
}

fn main() {
    assert_eq!(CONST_ALPHA.encode, *b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz");
    let (slices, arrays, vectors) = wrapper_cases();
    generic_boundary_witnesses();
    default_cases();
    println!("extension_native: slice_wrapper_cases={slices}; array_wrapper_cases={arrays}; max_length_cases=9; complete_buffers_on_ok_and_err=true");
    println!("extension_vectors: cases={vectors}; complete_success_and_error_states=true");
}
