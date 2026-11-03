use super::*;
use array::typenum::U16;
pub fn snapshot<B: ArraySize>(value: &PaddedData<'_, B>) -> (*const u8, usize, [u8; 16], [u8; 32]) {
    let PaddedData::Pad { blocks, tail_block } = value else {
        panic!("precondition")
    };
    let mut bytes = [0; 16];
    for i in 0..16 {
        bytes[i] = tail_block[i];
    }
    let mut prefix = [0; 32];
    for j in 0..2 {
        if j < blocks.len() {
            for i in 0..16 {
                prefix[j * 16 + i] = blocks[j][i];
            }
        }
    }
    (blocks.as_ptr().cast(), blocks.len(), bytes, prefix)
}
pub fn unwrap_ok<B: ArraySize>(
    value: &(&[Array<u8, B>], Array<u8, B>),
    old: (*const u8, usize, [u8; 16], [u8; 32]),
) -> bool {
    if value.0.as_ptr().cast::<u8>() != old.0 || value.0.len() != old.1 {
        return false;
    }
    for i in 0..16 {
        if value.1[i] != old.2[i] {
            return false;
        }
    }
    for j in 0..2 {
        if j < value.0.len() {
            for i in 0..16 {
                if value.0[j][i] != old.3[j * 16 + i] {
                    return false;
                }
            }
        }
    }
    true
}
#[kani::proof_for_contract(crate::PaddedData::unwrap)]
#[kani::unwind(35)]
fn unwrap_pad() {
    let bytes: [[u8; 16]; 3] = kani::any();
    let blocks: [Array<u8, U16>; 2] = [bytes[0].into(), bytes[1].into()];
    let n: usize = kani::any();
    kani::assume(n <= 2);
    let value = PaddedData::Pad {
        blocks: &blocks[..n],
        tail_block: bytes[2].into(),
    };
    let _ = value.unwrap();
}
fn decode(x: &[u8], kind: u8) -> Option<usize> {
    let n = x.len();
    if kind == 0 {
        let mut p = n;
        while p > 0 && x[p - 1] == 0 {
            p -= 1;
        }
        return Some(p);
    }
    if kind == 5 {
        return Some(n);
    }
    if kind == 4 {
        let mut p = n;
        while p > 0 {
            p -= 1;
            if x[p] == 128 {
                return Some(p);
            }
            if x[p] != 0 {
                return None;
            }
        }
        return None;
    }
    let c = x[n - 1] as usize;
    if c == 0 || c > n {
        return None;
    }
    for i in n - c..n - 1 {
        if (kind == 1 && x[i] != c as u8) || (kind == 3 && x[i] != 0) {
            return None;
        }
    }
    Some(n - c)
}
fn suffix(kind: u8, pos: usize, i: usize) -> u8 {
    match kind {
        0 => 0,
        1 | 2 => (16 - pos) as u8,
        3 => {
            if i == 15 {
                (16 - pos) as u8
            } else {
                0
            }
        }
        4 => {
            if i == pos {
                128
            } else {
                0
            }
        }
        _ => 0,
    }
}
fn typed_pad<P: Padding>(kind: u8) {
    let bytes: [u8; 16] = kani::any();
    let mut block: Array<u8, U16> = bytes.into();
    let p: usize = kani::any();
    kani::assume(if kind == 0 || kind == 5 {
        p <= 16
    } else {
        p < 16
    });
    P::pad(&mut block, p);
    for i in 0..16 {
        assert_eq!(
            block[i],
            if i < p || kind == 5 {
                bytes[i]
            } else {
                suffix(kind, p, i)
            }
        );
    }
}
fn typed_unpad<P: Padding>(kind: u8) {
    let bytes: [u8; 16] = kani::any();
    let block: Array<u8, U16> = bytes.into();
    let expected = decode(&bytes, kind);
    let actual = P::unpad(&block);
    match (expected, actual) {
        (Some(n), Ok(out)) => {
            assert_eq!(out.len(), n);
            assert_eq!(out.as_ptr(), block.as_ptr());
            for i in 0..n {
                assert_eq!(out[i], bytes[i]);
            }
        }
        (None, Err(_)) => {}
        _ => panic!("decode mismatch"),
    }
}
fn detached_all<P: Padding>(kind: u8) {
    let bytes: [u8; 32] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 32);
    let data = &bytes[..len];
    let q = len / 16;
    let r = len % 16;
    let result = P::pad_detached::<U16>(data);
    let blocks = match result {
        PaddedData::Error => {
            assert!(kind == 5 && r != 0);
            return;
        }
        PaddedData::NoPad { blocks } => {
            assert!((kind == 0 || kind == 5) && r == 0);
            blocks
        }
        PaddedData::Pad { blocks, tail_block } => {
            assert!(kind != 5 && (kind != 0 || r != 0));
            for i in 0..16 {
                assert_eq!(
                    tail_block[i],
                    if i < r {
                        bytes[q * 16 + i]
                    } else {
                        suffix(kind, r, i)
                    }
                );
            }
            blocks
        }
    };
    assert_eq!(blocks.len(), q);
    assert_eq!(blocks.as_ptr().cast::<u8>(), data.as_ptr());
    for j in 0..2 {
        if j < q {
            for i in 0..16 {
                assert_eq!(blocks[j][i], bytes[j * 16 + i]);
            }
        }
    }
}
fn blocks_all<P: Padding>(kind: u8) {
    let bytes: [[u8; 16]; 2] = kani::any();
    let blocks: [Array<u8, U16>; 2] = [bytes[0].into(), bytes[1].into()];
    let n: usize = kani::any();
    kani::assume(n <= 2);
    let mut flat = [0u8; 32];
    for j in 0..2 {
        for i in 0..16 {
            flat[j * 16 + i] = bytes[j][i];
        }
    }
    let expected = if kind == 0 || kind == 5 {
        decode(&flat[..n * 16], kind)
    } else if n == 0 {
        None
    } else {
        decode(&bytes[n - 1], kind).map(|p| (n - 1) * 16 + p)
    };
    let actual = P::unpad_blocks(&blocks[..n]);
    match (expected, actual) {
        (Some(p), Ok(out)) => {
            assert_eq!(out.len(), p);
            assert_eq!(out.as_ptr(), blocks.as_ptr().cast::<u8>());
            for i in 0..p {
                assert_eq!(out[i], flat[i]);
            }
        }
        (None, Err(_)) => {}
        _ => panic!("blocks mismatch"),
    }
}

#[kani::proof]
#[kani::unwind(35)]
fn zeropadding_typed_pad() {
    typed_pad::<ZeroPadding>(0);
}

#[kani::proof]
#[kani::unwind(35)]
fn zeropadding_typed_unpad() {
    typed_unpad::<ZeroPadding>(0);
}

#[kani::proof]
#[kani::unwind(35)]
fn zeropadding_detached_all() {
    detached_all::<ZeroPadding>(0);
}

#[kani::proof]
#[kani::unwind(35)]
fn zeropadding_blocks_all() {
    blocks_all::<ZeroPadding>(0);
}

#[kani::proof]
#[kani::unwind(35)]
fn pkcs7_typed_pad() {
    typed_pad::<Pkcs7>(1);
}

#[kani::proof]
#[kani::unwind(35)]
fn pkcs7_typed_unpad() {
    typed_unpad::<Pkcs7>(1);
}

#[kani::proof]
#[kani::unwind(35)]
fn pkcs7_detached_all() {
    detached_all::<Pkcs7>(1);
}

#[kani::proof]
#[kani::unwind(35)]
fn pkcs7_blocks_all() {
    blocks_all::<Pkcs7>(1);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso10126_typed_pad() {
    typed_pad::<Iso10126>(2);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso10126_typed_unpad() {
    typed_unpad::<Iso10126>(2);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso10126_detached_all() {
    detached_all::<Iso10126>(2);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso10126_blocks_all() {
    blocks_all::<Iso10126>(2);
}

#[kani::proof]
#[kani::unwind(35)]
fn ansix923_typed_pad() {
    typed_pad::<AnsiX923>(3);
}

#[kani::proof]
#[kani::unwind(35)]
fn ansix923_typed_unpad() {
    typed_unpad::<AnsiX923>(3);
}

#[kani::proof]
#[kani::unwind(35)]
fn ansix923_detached_all() {
    detached_all::<AnsiX923>(3);
}

#[kani::proof]
#[kani::unwind(35)]
fn ansix923_blocks_all() {
    blocks_all::<AnsiX923>(3);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso7816_typed_pad() {
    typed_pad::<Iso7816>(4);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso7816_typed_unpad() {
    typed_unpad::<Iso7816>(4);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso7816_detached_all() {
    detached_all::<Iso7816>(4);
}

#[kani::proof]
#[kani::unwind(35)]
fn iso7816_blocks_all() {
    blocks_all::<Iso7816>(4);
}

#[kani::proof]
#[kani::unwind(35)]
fn nopadding_typed_pad() {
    typed_pad::<NoPadding>(5);
}

#[kani::proof]
#[kani::unwind(35)]
fn nopadding_typed_unpad() {
    typed_unpad::<NoPadding>(5);
}

#[kani::proof]
#[kani::unwind(35)]
fn nopadding_detached_all() {
    detached_all::<NoPadding>(5);
}

#[kani::proof]
#[kani::unwind(35)]
fn nopadding_blocks_all() {
    blocks_all::<NoPadding>(5);
}
