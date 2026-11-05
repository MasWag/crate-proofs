#[path = "source/src/unindent.rs"] mod release;
#[path = "adapted/src/lib.rs"] mod adapted;
fn visit(input: &mut Vec<u8>, depth: usize, count: &mut usize) {
    assert_eq!(release::unindent_bytes(input), adapted::unindent_bytes(input), "{input:?}");
    *count += 1;
    if depth > 0 {
        for ch in [b' ', b'\t', b'\n', b'\r', b'A', 0, 255] {
            input.push(ch); visit(input, depth-1, count); input.pop();
        }
    }
}
fn main() { let mut count = 0; visit(&mut Vec::new(), 7, &mut count);
    println!("Matched {count} byte inputs, all lengths 0..=7 over SPACE,TAB,LF,CR,A,NUL,FF."); }
