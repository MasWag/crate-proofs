#[path = "../../.work/source/src/unindent.rs"]
mod release;
use unindent::{unindent_bytes,Unindent};
#[test]
fn arbitrary_bytes_differential() {
    let alphabet = [0,9,10,13,32,65,128,255];
    let mut count = 0;
    for len in 0..=6 {
        let mut input = vec![0;len];
        for mut code in 0..alphabet.len().pow(len as u32) {
            for byte in &mut input { *byte = alphabet[code % alphabet.len()]; code /= alphabet.len(); }
            assert_eq!(unindent_bytes(&input),release::unindent_bytes(&input),"{input:?}");
            assert_eq!(input.as_slice().unindent(),release::unindent_bytes(&input));
            count+=1;
        }
    }
    let mut state = 0xbadc0ffee1234567u64;
    for len in 0..1024 {
        let mut input = Vec::new();
        for _ in 0..len {
            state ^= state << 13; state ^= state >> 7; state ^= state << 17;
            let byte = match state & 7 { 0=>9,1=>10,2=>13,3=>32,_=>(state >> 8) as u8 };
            input.push(byte);
        }
        assert_eq!(unindent_bytes(&input),release::unindent_bytes(&input),"length {len}");
        count+=1;
    }
    println!("native byte differential cases={count}");
}
#[test]
fn unicode_strings_differential() {
    let alphabet = ['\0','\t','\n','\r',' ','A','é','🦀'];
    let mut count = 0;
    for len in 0..=6 {
        for mut code in 0..alphabet.len().pow(len as u32) {
            let mut input = String::new();
            for _ in 0..len { input.push(alphabet[code % alphabet.len()]); code /= alphabet.len(); }
            let expected = release::unindent(&input);
            assert_eq!(unindent::unindent(&input),expected,"{input:?}");
            assert_eq!(input.as_str().unindent(),expected);
            assert_eq!(input.unindent(),expected);
            count += 1;
        }
    }
    println!("native string differential cases={count}");
}
