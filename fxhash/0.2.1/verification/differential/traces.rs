//! Finite differential checks of the release and the explicit Rust adaptation.
//! These checks are not a universal equivalence proof.
use std::hash::Hasher;

fn compare_trace<A: Hasher + Default, B: Hasher + Default>() {
    for len in 0..=257 {
        let bytes: Vec<u8> = (0..len).map(|i| ((i * 197 + len * 31) % 256) as u8).collect();
        for split in 0..=len {
            let (mut a, mut b) = (A::default(), B::default());
            assert_eq!(a.finish(), b.finish());
            a.write_u64(u64::MAX - len as u64);
            b.write_u64(u64::MAX - len as u64);
            a.write(&bytes[..split]);
            b.write(&bytes[..split]);
            assert_eq!(a.finish(), b.finish(), "len={len}, split={split}, first");
            let observed = a.finish();
            assert_eq!(a.finish(), observed, "finish must not reset state");
            a.write(&bytes[split..]);
            b.write(&bytes[split..]);
            a.write(&[]);
            b.write(&[]);
            assert_eq!(a.finish(), b.finish(), "len={len}, split={split}, second");
            for value in [0, 1, 255, 256, u32::MAX as u64, 1 << 32, 1 << 63, u64::MAX] {
                a.write_u8(value as u8); b.write_u8(value as u8);
                a.write_u16(value as u16); b.write_u16(value as u16);
                a.write_u32(value as u32); b.write_u32(value as u32);
                a.write_u64(value); b.write_u64(value);
                a.write_usize(value as usize); b.write_usize(value as usize);
                assert_eq!(a.finish(), b.finish(), "len={len}, split={split}, integer={value}");
            }
        }
    }
}

#[test]
fn native_traces() { compare_trace::<release_fx::FxHasher, adapted_fx::FxHasher>(); }
#[test]
fn width32_traces() { compare_trace::<release_fx::FxHasher32, adapted_fx::FxHasher32>(); }
#[test]
fn width64_traces() { compare_trace::<release_fx::FxHasher64, adapted_fx::FxHasher64>(); }
