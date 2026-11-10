// Checked decimal specialization of locked release SWAR bodies.
pub fn is_4digits(v: u32) -> bool {
    let radix = 10u32;
    debug_assert!(radix <= 10);

    // We want to have a wrapping add and sub such that only values from the
    // range `[0x30, 0x39]` (or narrower for custom radixes) will not
    // overflow into the high bit. This means that the value needs to overflow
    // into into `0x80` if the digit is 1 above, or `0x46` for the value `0x39`.
    // Likewise, we only valid for `[0x30, 0x38]` for radix 8, so we need
    // `0x47`.
    let add = 0x46 + 10 - radix;
    let add = add + (add << 8) + (add << 16) + (add << 24);
    // This aims to underflow if anything is below the min digit: if we have any
    // values under `0x30`, then this underflows and wraps into the high bit.
    let sub = 0x3030_3030;
    let a = v.wrapping_add(add);
    let b = v.wrapping_sub(sub);

    (a | b) & 0x8080_8080 == 0
}

pub fn parse_4digits(mut v: u32) -> u32 {
    let radix = 10u32;
    debug_assert!(radix <= 10);

    // Normalize our digits to the range `[0, 9]`.
    v -= 0x3030_3030;
    // Scale digits in `0 <= Nn <= 99`.
    v = (v * radix) + (v >> 8);
    // Scale digits in `0 <= Nnnn <= 9999`.
    v = ((v & 0x0000007f) * radix * radix) + ((v >> 16) & 0x0000007f);

    v
}

pub fn is_8digits(v: u64) -> bool {
    let radix = 10u32;
    debug_assert!(radix <= 10);

    let add = 0x46 + 10 - radix;
    let add = add + (add << 8) + (add << 16) + (add << 24);
    let add = (add as u64) | ((add as u64) << 32);
    // This aims to underflow if anything is below the min digit: if we have any
    // values under `0x30`, then this underflows and wraps into the high bit.
    let sub = 0x3030_3030_3030_3030;
    let a = v.wrapping_add(add);
    let b = v.wrapping_sub(sub);

    (a | b) & 0x8080_8080_8080_8080 == 0
}

pub fn parse_8digits(mut v: u64) -> u64 {
    let radix = 10u32 as u64;
    debug_assert!(radix <= 10);

    // Create our masks. Assume the optimizer will do this at compile time.
    // It seems like an optimizing compiler **will** do this, so we
    // should be safe.
    let radix2 = radix * radix;
    let radix4 = radix2 * radix2;
    let radix6 = radix2 * radix4;
    let mask = 0x0000_00FF_0000_00FFu64;
    let mul1 = radix2 + (radix6 << 32);
    let mul2 = 1 + (radix4 << 32);

    // Normalize our digits to the base.
    v -= 0x3030_3030_3030_3030;
    // Scale digits in `0 <= Nn <= 99`.
    v = (v * radix) + (v >> 8);
    let v1 = (v & mask).wrapping_mul(mul1);
    let v2 = ((v >> 16) & mask).wrapping_mul(mul2);

    ((v1.wrapping_add(v2) >> 32) as u32) as u64
}
