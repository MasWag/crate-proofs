#![allow(deprecated, unstable_name_collisions)]
use num_conv::{Extend, Truncate, Widen};
#[test]
fn all_declared_instances_boundaries() {
    for x in [u8::MIN, u8::MAX, 0, 1] {
        let w: u8 = x.widen();
        let e: u8 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [u8::MIN, u8::MAX, 0, 1, u8::MAX as u8] {
        let lo = u8::MIN as u8;
        let hi = u8::MAX as u8;
        let sat: u8 = x.saturating_truncate();
        let checked: Option<u8> = x.checked_truncate();
        let wrapped: u8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u8::MIN, u8::MAX, 0, 1] {
        let w: u16 = x.widen();
        let e: u16 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u16::MIN,
        u16::MAX,
        0,
        1,
        u8::MAX as u16,
        (u8::MAX as u16) + 1,
    ] {
        let lo = u8::MIN as u16;
        let hi = u8::MAX as u16;
        let sat: u8 = x.saturating_truncate();
        let checked: Option<u8> = x.checked_truncate();
        let wrapped: u8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u8::MIN, u8::MAX, 0, 1] {
        let w: u32 = x.widen();
        let e: u32 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u32::MIN,
        u32::MAX,
        0,
        1,
        u8::MAX as u32,
        (u8::MAX as u32) + 1,
    ] {
        let lo = u8::MIN as u32;
        let hi = u8::MAX as u32;
        let sat: u8 = x.saturating_truncate();
        let checked: Option<u8> = x.checked_truncate();
        let wrapped: u8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u8::MIN, u8::MAX, 0, 1] {
        let w: u64 = x.widen();
        let e: u64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u64::MIN,
        u64::MAX,
        0,
        1,
        u8::MAX as u64,
        (u8::MAX as u64) + 1,
    ] {
        let lo = u8::MIN as u64;
        let hi = u8::MAX as u64;
        let sat: u8 = x.saturating_truncate();
        let checked: Option<u8> = x.checked_truncate();
        let wrapped: u8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u8::MIN, u8::MAX, 0, 1] {
        let w: u128 = x.widen();
        let e: u128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u128::MIN,
        u128::MAX,
        0,
        1,
        u8::MAX as u128,
        (u8::MAX as u128) + 1,
    ] {
        let lo = u8::MIN as u128;
        let hi = u8::MAX as u128;
        let sat: u8 = x.saturating_truncate();
        let checked: Option<u8> = x.checked_truncate();
        let wrapped: u8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u8::MIN, u8::MAX, 0, 1] {
        let w: usize = x.widen();
        let e: usize = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        usize::MIN,
        usize::MAX,
        0,
        1,
        u8::MAX as usize,
        (u8::MAX as usize) + 1,
    ] {
        let lo = u8::MIN as usize;
        let hi = u8::MAX as usize;
        let sat: u8 = x.saturating_truncate();
        let checked: Option<u8> = x.checked_truncate();
        let wrapped: u8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u16::MIN, u16::MAX, 0, 1] {
        let w: u16 = x.widen();
        let e: u16 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [u16::MIN, u16::MAX, 0, 1, u16::MAX as u16] {
        let lo = u16::MIN as u16;
        let hi = u16::MAX as u16;
        let sat: u16 = x.saturating_truncate();
        let checked: Option<u16> = x.checked_truncate();
        let wrapped: u16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u16::MIN, u16::MAX, 0, 1] {
        let w: u32 = x.widen();
        let e: u32 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u32::MIN,
        u32::MAX,
        0,
        1,
        u16::MAX as u32,
        (u16::MAX as u32) + 1,
    ] {
        let lo = u16::MIN as u32;
        let hi = u16::MAX as u32;
        let sat: u16 = x.saturating_truncate();
        let checked: Option<u16> = x.checked_truncate();
        let wrapped: u16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u16::MIN, u16::MAX, 0, 1] {
        let w: u64 = x.widen();
        let e: u64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u64::MIN,
        u64::MAX,
        0,
        1,
        u16::MAX as u64,
        (u16::MAX as u64) + 1,
    ] {
        let lo = u16::MIN as u64;
        let hi = u16::MAX as u64;
        let sat: u16 = x.saturating_truncate();
        let checked: Option<u16> = x.checked_truncate();
        let wrapped: u16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u16::MIN, u16::MAX, 0, 1] {
        let w: u128 = x.widen();
        let e: u128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u128::MIN,
        u128::MAX,
        0,
        1,
        u16::MAX as u128,
        (u16::MAX as u128) + 1,
    ] {
        let lo = u16::MIN as u128;
        let hi = u16::MAX as u128;
        let sat: u16 = x.saturating_truncate();
        let checked: Option<u16> = x.checked_truncate();
        let wrapped: u16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u16::MIN, u16::MAX, 0, 1] {
        let w: usize = x.widen();
        let e: usize = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        usize::MIN,
        usize::MAX,
        0,
        1,
        u16::MAX as usize,
        (u16::MAX as usize) + 1,
    ] {
        let lo = u16::MIN as usize;
        let hi = u16::MAX as usize;
        let sat: u16 = x.saturating_truncate();
        let checked: Option<u16> = x.checked_truncate();
        let wrapped: u16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u32::MIN, u32::MAX, 0, 1] {
        let w: u32 = x.widen();
        let e: u32 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [u32::MIN, u32::MAX, 0, 1, u32::MAX as u32] {
        let lo = u32::MIN as u32;
        let hi = u32::MAX as u32;
        let sat: u32 = x.saturating_truncate();
        let checked: Option<u32> = x.checked_truncate();
        let wrapped: u32 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u32::MIN, u32::MAX, 0, 1] {
        let w: u64 = x.widen();
        let e: u64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u64::MIN,
        u64::MAX,
        0,
        1,
        u32::MAX as u64,
        (u32::MAX as u64) + 1,
    ] {
        let lo = u32::MIN as u64;
        let hi = u32::MAX as u64;
        let sat: u32 = x.saturating_truncate();
        let checked: Option<u32> = x.checked_truncate();
        let wrapped: u32 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u32::MIN, u32::MAX, 0, 1] {
        let w: u128 = x.widen();
        let e: u128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u128::MIN,
        u128::MAX,
        0,
        1,
        u32::MAX as u128,
        (u32::MAX as u128) + 1,
    ] {
        let lo = u32::MIN as u128;
        let hi = u32::MAX as u128;
        let sat: u32 = x.saturating_truncate();
        let checked: Option<u32> = x.checked_truncate();
        let wrapped: u32 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u64::MIN, u64::MAX, 0, 1] {
        let w: u64 = x.widen();
        let e: u64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [u64::MIN, u64::MAX, 0, 1, u64::MAX as u64] {
        let lo = u64::MIN as u64;
        let hi = u64::MAX as u64;
        let sat: u64 = x.saturating_truncate();
        let checked: Option<u64> = x.checked_truncate();
        let wrapped: u64 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u64::MIN, u64::MAX, 0, 1] {
        let w: u128 = x.widen();
        let e: u128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        u128::MIN,
        u128::MAX,
        0,
        1,
        u64::MAX as u128,
        (u64::MAX as u128) + 1,
    ] {
        let lo = u64::MIN as u128;
        let hi = u64::MAX as u128;
        let sat: u64 = x.saturating_truncate();
        let checked: Option<u64> = x.checked_truncate();
        let wrapped: u64 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [u128::MIN, u128::MAX, 0, 1] {
        let w: u128 = x.widen();
        let e: u128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [u128::MIN, u128::MAX, 0, 1, u128::MAX as u128] {
        let lo = u128::MIN as u128;
        let hi = u128::MAX as u128;
        let sat: u128 = x.saturating_truncate();
        let checked: Option<u128> = x.checked_truncate();
        let wrapped: u128 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [usize::MIN, usize::MAX, 0, 1] {
        let w: usize = x.widen();
        let e: usize = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [usize::MIN, usize::MAX, 0, 1, usize::MAX as usize] {
        let lo = usize::MIN as usize;
        let hi = usize::MAX as usize;
        let sat: usize = x.saturating_truncate();
        let checked: Option<usize> = x.checked_truncate();
        let wrapped: usize = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1] {
        let w: i8 = x.widen();
        let e: i8 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1, i8::MIN as i8, i8::MAX as i8] {
        let lo = i8::MIN as i8;
        let hi = i8::MAX as i8;
        let sat: i8 = x.saturating_truncate();
        let checked: Option<i8> = x.checked_truncate();
        let wrapped: i8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1] {
        let w: i16 = x.widen();
        let e: i16 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i16::MIN,
        i16::MAX,
        0,
        1,
        -1,
        i8::MIN as i16,
        i8::MAX as i16,
        (i8::MAX as i16) + 1,
        (i8::MIN as i16) - 1,
    ] {
        let lo = i8::MIN as i16;
        let hi = i8::MAX as i16;
        let sat: i8 = x.saturating_truncate();
        let checked: Option<i8> = x.checked_truncate();
        let wrapped: i8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1] {
        let w: i32 = x.widen();
        let e: i32 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i32::MIN,
        i32::MAX,
        0,
        1,
        -1,
        i8::MIN as i32,
        i8::MAX as i32,
        (i8::MAX as i32) + 1,
        (i8::MIN as i32) - 1,
    ] {
        let lo = i8::MIN as i32;
        let hi = i8::MAX as i32;
        let sat: i8 = x.saturating_truncate();
        let checked: Option<i8> = x.checked_truncate();
        let wrapped: i8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1] {
        let w: i64 = x.widen();
        let e: i64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i64::MIN,
        i64::MAX,
        0,
        1,
        -1,
        i8::MIN as i64,
        i8::MAX as i64,
        (i8::MAX as i64) + 1,
        (i8::MIN as i64) - 1,
    ] {
        let lo = i8::MIN as i64;
        let hi = i8::MAX as i64;
        let sat: i8 = x.saturating_truncate();
        let checked: Option<i8> = x.checked_truncate();
        let wrapped: i8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1] {
        let w: i128 = x.widen();
        let e: i128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i128::MIN,
        i128::MAX,
        0,
        1,
        -1,
        i8::MIN as i128,
        i8::MAX as i128,
        (i8::MAX as i128) + 1,
        (i8::MIN as i128) - 1,
    ] {
        let lo = i8::MIN as i128;
        let hi = i8::MAX as i128;
        let sat: i8 = x.saturating_truncate();
        let checked: Option<i8> = x.checked_truncate();
        let wrapped: i8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i8::MIN, i8::MAX, 0, 1, -1] {
        let w: isize = x.widen();
        let e: isize = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        isize::MIN,
        isize::MAX,
        0,
        1,
        -1,
        i8::MIN as isize,
        i8::MAX as isize,
        (i8::MAX as isize) + 1,
        (i8::MIN as isize) - 1,
    ] {
        let lo = i8::MIN as isize;
        let hi = i8::MAX as isize;
        let sat: i8 = x.saturating_truncate();
        let checked: Option<i8> = x.checked_truncate();
        let wrapped: i8 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i16::MIN, i16::MAX, 0, 1, -1] {
        let w: i16 = x.widen();
        let e: i16 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i16::MIN,
        i16::MAX,
        0,
        1,
        -1,
        i16::MIN as i16,
        i16::MAX as i16,
    ] {
        let lo = i16::MIN as i16;
        let hi = i16::MAX as i16;
        let sat: i16 = x.saturating_truncate();
        let checked: Option<i16> = x.checked_truncate();
        let wrapped: i16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i16::MIN, i16::MAX, 0, 1, -1] {
        let w: i32 = x.widen();
        let e: i32 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i32::MIN,
        i32::MAX,
        0,
        1,
        -1,
        i16::MIN as i32,
        i16::MAX as i32,
        (i16::MAX as i32) + 1,
        (i16::MIN as i32) - 1,
    ] {
        let lo = i16::MIN as i32;
        let hi = i16::MAX as i32;
        let sat: i16 = x.saturating_truncate();
        let checked: Option<i16> = x.checked_truncate();
        let wrapped: i16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i16::MIN, i16::MAX, 0, 1, -1] {
        let w: i64 = x.widen();
        let e: i64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i64::MIN,
        i64::MAX,
        0,
        1,
        -1,
        i16::MIN as i64,
        i16::MAX as i64,
        (i16::MAX as i64) + 1,
        (i16::MIN as i64) - 1,
    ] {
        let lo = i16::MIN as i64;
        let hi = i16::MAX as i64;
        let sat: i16 = x.saturating_truncate();
        let checked: Option<i16> = x.checked_truncate();
        let wrapped: i16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i16::MIN, i16::MAX, 0, 1, -1] {
        let w: i128 = x.widen();
        let e: i128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i128::MIN,
        i128::MAX,
        0,
        1,
        -1,
        i16::MIN as i128,
        i16::MAX as i128,
        (i16::MAX as i128) + 1,
        (i16::MIN as i128) - 1,
    ] {
        let lo = i16::MIN as i128;
        let hi = i16::MAX as i128;
        let sat: i16 = x.saturating_truncate();
        let checked: Option<i16> = x.checked_truncate();
        let wrapped: i16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i16::MIN, i16::MAX, 0, 1, -1] {
        let w: isize = x.widen();
        let e: isize = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        isize::MIN,
        isize::MAX,
        0,
        1,
        -1,
        i16::MIN as isize,
        i16::MAX as isize,
        (i16::MAX as isize) + 1,
        (i16::MIN as isize) - 1,
    ] {
        let lo = i16::MIN as isize;
        let hi = i16::MAX as isize;
        let sat: i16 = x.saturating_truncate();
        let checked: Option<i16> = x.checked_truncate();
        let wrapped: i16 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i32::MIN, i32::MAX, 0, 1, -1] {
        let w: i32 = x.widen();
        let e: i32 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i32::MIN,
        i32::MAX,
        0,
        1,
        -1,
        i32::MIN as i32,
        i32::MAX as i32,
    ] {
        let lo = i32::MIN as i32;
        let hi = i32::MAX as i32;
        let sat: i32 = x.saturating_truncate();
        let checked: Option<i32> = x.checked_truncate();
        let wrapped: i32 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i32::MIN, i32::MAX, 0, 1, -1] {
        let w: i64 = x.widen();
        let e: i64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i64::MIN,
        i64::MAX,
        0,
        1,
        -1,
        i32::MIN as i64,
        i32::MAX as i64,
        (i32::MAX as i64) + 1,
        (i32::MIN as i64) - 1,
    ] {
        let lo = i32::MIN as i64;
        let hi = i32::MAX as i64;
        let sat: i32 = x.saturating_truncate();
        let checked: Option<i32> = x.checked_truncate();
        let wrapped: i32 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i32::MIN, i32::MAX, 0, 1, -1] {
        let w: i128 = x.widen();
        let e: i128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i128::MIN,
        i128::MAX,
        0,
        1,
        -1,
        i32::MIN as i128,
        i32::MAX as i128,
        (i32::MAX as i128) + 1,
        (i32::MIN as i128) - 1,
    ] {
        let lo = i32::MIN as i128;
        let hi = i32::MAX as i128;
        let sat: i32 = x.saturating_truncate();
        let checked: Option<i32> = x.checked_truncate();
        let wrapped: i32 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i64::MIN, i64::MAX, 0, 1, -1] {
        let w: i64 = x.widen();
        let e: i64 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i64::MIN,
        i64::MAX,
        0,
        1,
        -1,
        i64::MIN as i64,
        i64::MAX as i64,
    ] {
        let lo = i64::MIN as i64;
        let hi = i64::MAX as i64;
        let sat: i64 = x.saturating_truncate();
        let checked: Option<i64> = x.checked_truncate();
        let wrapped: i64 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i64::MIN, i64::MAX, 0, 1, -1] {
        let w: i128 = x.widen();
        let e: i128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i128::MIN,
        i128::MAX,
        0,
        1,
        -1,
        i64::MIN as i128,
        i64::MAX as i128,
        (i64::MAX as i128) + 1,
        (i64::MIN as i128) - 1,
    ] {
        let lo = i64::MIN as i128;
        let hi = i64::MAX as i128;
        let sat: i64 = x.saturating_truncate();
        let checked: Option<i64> = x.checked_truncate();
        let wrapped: i64 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [i128::MIN, i128::MAX, 0, 1, -1] {
        let w: i128 = x.widen();
        let e: i128 = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        i128::MIN,
        i128::MAX,
        0,
        1,
        -1,
        i128::MIN as i128,
        i128::MAX as i128,
    ] {
        let lo = i128::MIN as i128;
        let hi = i128::MAX as i128;
        let sat: i128 = x.saturating_truncate();
        let checked: Option<i128> = x.checked_truncate();
        let wrapped: i128 = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
    for x in [isize::MIN, isize::MAX, 0, 1, -1] {
        let w: isize = x.widen();
        let e: isize = x.extend();
        assert_eq!(w.to_string(), x.to_string());
        assert_eq!(e.to_string(), x.to_string());
    }
    for x in [
        isize::MIN,
        isize::MAX,
        0,
        1,
        -1,
        isize::MIN as isize,
        isize::MAX as isize,
    ] {
        let lo = isize::MIN as isize;
        let hi = isize::MAX as isize;
        let sat: isize = x.saturating_truncate();
        let checked: Option<isize> = x.checked_truncate();
        let wrapped: isize = x.truncate();
        let clamped = x.clamp(lo, hi);
        assert_eq!(sat.to_string(), clamped.to_string());
        if (lo..=hi).contains(&x) {
            assert_eq!(checked.unwrap().to_string(), x.to_string());
            assert_eq!(wrapped.to_string(), x.to_string());
        } else {
            assert!(checked.is_none());
        }
        assert_eq!(
            &wrapped.to_le_bytes()[..],
            &x.to_le_bytes()[..core::mem::size_of_val(&wrapped)]
        );
    }
}
#[test]
fn exhaustive_sixteen_to_eight() {
    for x in u16::MIN..=u16::MAX {
        let c: Option<u8> = x.checked_truncate();
        let s: u8 = x.saturating_truncate();
        let w: u8 = x.truncate();
        assert_eq!(u16::from(w), x % 256);
        assert_eq!(u16::from(s), x.min(255));
        assert_eq!(c.map(u16::from), if x <= 255 { Some(x) } else { None });
    }
    for x in i16::MIN..=i16::MAX {
        let c: Option<i8> = x.checked_truncate();
        let s: i8 = x.saturating_truncate();
        let w: i8 = x.truncate();
        assert_eq!(i32::from(w), (i32::from(x) + 128).rem_euclid(256) - 128);
        assert_eq!(i16::from(s), x.clamp(-128, 127));
        assert_eq!(
            c.map(i16::from),
            if (-128..=127).contains(&x) {
                Some(x)
            } else {
                None
            }
        );
    }
}
