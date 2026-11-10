use lexical_core_compact_write::{decimal_u8, release_compact_u8};

#[test]
fn all_u8_values_match_release_and_public_facade() {
    let mut comparisons = 0;
    for value in 0..=u8::MAX {
        let expected = value.to_string();
        for capacity in [3, 4, 16, 127, 128, 129] {
            for seed in [0u8, 0x55, 0xff] {
                let initial: Vec<u8> = (0..capacity)
                    .map(|i| seed.wrapping_add((i as u8).wrapping_mul(17)))
                    .collect();
                let mut derived = initial.clone();
                let mut release = initial.clone();
                let mut facade = initial.clone();
                let k = decimal_u8(value, &mut derived);
                let release_k = release_compact_u8(value, &mut release);
                let written = lexical_core::write(value, &mut facade);
                assert_eq!(k, expected.len());
                assert_eq!(release_k, k);
                assert_eq!(written, expected.as_bytes());
                assert_eq!(&derived[..k], expected.as_bytes());
                assert_eq!(derived, release);
                assert_eq!(derived, facade);
                assert_eq!(&derived[k..], &initial[k..]);
                comparisons += 1;
            }
        }
    }
    println!("{comparisons} comparisons: all 256 u8 values, six buffer lengths, three initial patterns");
}
