extern crate utf8;
use std::panic::catch_unwind;
use utf8::Incomplete;
fn main() {
    for bytes in [&[0x61, 0xff][..], &[0xff, 0xff], &[0xe2, 0x82]] {
        let failed = catch_unwind(|| {
            let mut pending = Incomplete::new(bytes);
            let r = pending.try_complete(&[]);
            println!("returned {r:?}");
        }).is_err();
        println!("{bytes:02x?} panicked={failed}");
    }
}
