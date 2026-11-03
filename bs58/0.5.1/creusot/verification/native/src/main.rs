use bs58_creusot as fork;
use bs58_upstream as upstream;
use sha2::{Digest, Sha256};

const CONST_ALPHA: fork::Alphabet = match fork::Alphabet::new(
    b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
) {
    Ok(alpha) => alpha,
    Err(_) => panic!("valid Bitcoin alphabet rejected"),
};
const CONST_EMPTY: [u8; 0] = match fork::decode_into_const::<0>(&[], &CONST_ALPHA) {
    Ok(output) => output,
    Err(_) => panic!("empty const decoding rejected"),
};
const CONST_PADDED: [u8; 4] = match fork::decode_into_const::<4>(b"112", &CONST_ALPHA) {
    Ok(output) => output,
    Err(_) => panic!("const decoding with leading zeros rejected"),
};
const UPSTREAM_CONST_PADDED: [u8; 4] =
    match upstream::decode(b"112".as_slice()).into_array_const::<4>() {
        Ok(output) => output,
        Err(_) => panic!("upstream const decoding rejected"),
    };
const _: () = {
    assert!(CONST_EMPTY.len() == 0);
    assert!(CONST_PADDED[0] == 0 && CONST_PADDED[1] == 0);
    assert!(CONST_PADDED[2] == 1 && CONST_PADDED[3] == 0);
};

fn same<T: core::fmt::Debug, U: core::fmt::Debug>(left: T, right: U) {
    assert_eq!(format!("{left:?}"), format!("{right:?}"));
}

fn compare(input: &[u8], base: &[u8; 58], capacity: usize) {
    let original = upstream::Alphabet::new(base).unwrap();
    let adapted = fork::Alphabet::new(base).unwrap();
    let mut a = vec![0xa5; capacity];
    let mut b = a.clone();
    same(upstream::encode(input).with_alphabet(&original).onto(&mut a[..]),
         fork::encode_into(input, &mut b, &adapted));
    assert_eq!(a, b, "encode post-state for {input:?}, capacity {capacity}");
    a.fill(0xa5);
    b.fill(0xa5);
    same(upstream::decode(input).with_alphabet(&original).onto(&mut a[..]),
         fork::decode_into(input, &mut b, &adapted));
    assert_eq!(a, b, "decode post-state for {input:?}, capacity {capacity}");
}

fn compare_const<const N: usize>(input: &[u8], base: &[u8; 58]) {
    let original = upstream::Alphabet::new(base).unwrap();
    let adapted = fork::Alphabet::new(base).unwrap();
    same(upstream::decode(input).with_alphabet(&original).into_array_const::<N>(),
         fork::decode_into_const::<N>(input, &adapted));
}

fn next(seed: &mut u64) -> u8 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed as u8
}

fn differential() {
    let mut alphabets = vec![
        *b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz",
        *b"123456789abcdefghijkmnopqrstuvwxyzABCDEFGHJKLMNPQRSTUVWXYZ",
    ];
    let mut unusual = [0; 58];
    for (i, byte) in unusual.iter_mut().enumerate() { *byte = i as u8; }
    alphabets.push(unusual);
    let mut seed = 0x58c0_dec0_051u64;
    let mut comparisons = 0usize;
    for base in alphabets {
        for i in 0..58 {
            let mut duplicate = base;
            duplicate[i] = duplicate[0];
            same(upstream::Alphabet::new(&duplicate).map(|_| ()),
                 fork::Alphabet::new(&duplicate).map(|_| ()));
            let mut non_ascii = base;
            non_ascii[i] = 128 + (i as u8);
            same(upstream::Alphabet::new(&non_ascii).map(|_| ()),
                 fork::Alphabet::new(&non_ascii).map(|_| ()));
        }
        let original = upstream::Alphabet::new(&base).unwrap();
        for iteration in 0..4000 {
            let length = (next(&mut seed) as usize) % 65;
            let mut input = vec![0; length];
            for byte in &mut input { *byte = next(&mut seed); }
            if iteration % 3 == 0 {
                let zeros = length.min(iteration % 17);
                input[..zeros].fill(0);
            }
            let encoded = upstream::encode(&input).with_alphabet(&original).into_vec();
            for candidate in [&input[..], &encoded[..]] {
                let mut capacities = vec![0, 1, length, encoded.len(), length + 8, encoded.len() + 8];
                capacities.sort_unstable();
                capacities.dedup();
                for capacity in capacities {
                    compare(candidate, &base, capacity);
                    comparisons += 1;
                }
                compare_const::<0>(candidate, &base);
                compare_const::<1>(candidate, &base);
                compare_const::<8>(candidate, &base);
                compare_const::<64>(candidate, &base);
                compare_const::<128>(candidate, &base);
            }
        }
        for byte in 0..=255 {
            for capacity in [0, 1, 2, 8] {
                compare(&[byte], &base, capacity);
                compare(&[base[57], byte], &base, capacity);
                comparisons += 2;
            }
        }
    }
    println!("differential: {comparisons} paired codec cases; compared complete buffers on both Ok and Err; fixed-array capacities 0,1,8,64,128 also checked");
}

fn checksum_findings() {
    for cb58 in [false, true] {
        let label = if cb58 { "CB58" } else { "Base58Check" };
        let encoded = if cb58 { upstream::encode([]).as_cb58(None).into_string() }
                      else { upstream::encode([]).with_check().into_string() };
        let raw = upstream::decode(&encoded).into_vec().unwrap();
        assert_eq!(raw.len(), 4);
        let result = if cb58 { upstream::decode(&encoded).as_cb58(Some(raw[0])).into_vec() }
                     else { upstream::decode(&encoded).with_check(Some(raw[0])).into_vec() };
        assert_eq!(result, Ok(vec![]));
        println!("F1 {label}: {encoded:?} accepted version {} with no payload", raw[0]);
        let encoded = if cb58 { upstream::encode([42]).as_cb58(None).into_string() }
                      else { upstream::encode([42]).with_check().into_string() };
        let mut output = [0xa5;16];
        let result = if cb58 { upstream::decode(&encoded).as_cb58(None).onto(&mut output) }
                     else { upstream::decode(&encoded).with_check(None).onto(&mut output) };
        assert_eq!(result, Ok(1));
        let written = if cb58 { [42, 95, 73, 79, 193] }
                      else { [42, 255, 18, 44, 14] };
        assert_eq!(&output[..5], &written);
        assert!(output[1..5].iter().all(|byte| *byte != 0xa5));
        assert_eq!(&output[5..], &[0xa5;11]);
        println!("F2 {label}: returned 1; modified prefix {:?}", &output[..5]);
        let first = Sha256::digest([42]);
        let computed: [u8;4] = if cb58 { first[28..].try_into().unwrap() }
                              else { Sha256::digest(first)[..4].try_into().unwrap() };
        let malformed = upstream::encode([42,0,0,0,0]).into_string();
        let result = if cb58 { upstream::decode(malformed).as_cb58(None).into_vec() }
                     else { upstream::decode(malformed).with_check(None).into_vec() };
        assert_eq!(result, Err(upstream::decode::Error::InvalidChecksum {
            checksum: computed, expected_checksum: [0;4]
        }));
        println!("F3 {label}: checksum={computed:?} (computed), expected_checksum=[0, 0, 0, 0] (given)");
    }
}

fn main() {
    assert_eq!(CONST_PADDED, UPSTREAM_CONST_PADDED);
    match std::env::args().nth(1).as_deref() {
        Some("--findings") => checksum_findings(),
        Some("--differential") => differential(),
        None => { differential(); checksum_findings(); }
        Some(other) => panic!("unknown argument: {other}"),
    }
}
