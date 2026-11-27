extern crate utf8;

fn main() {
    let mut state = utf8::Incomplete::new(&[0x61, 0xff]);
    let _ = state.try_complete(&[]);
}
