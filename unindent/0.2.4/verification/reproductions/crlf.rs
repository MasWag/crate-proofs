fn main() {
    let lf = "\n    a\n\n    b";
    let crlf = "\r\n    a\r\n\r\n    b";
    assert_eq!(unindent::unindent(lf), "a\n\nb");
    assert_eq!(unindent::unindent(crlf), "    a\r\n\r\n    b");
    println!("LF: {:?}", unindent::unindent(lf));
    println!("CRLF: {:?}", unindent::unindent(crlf));
}
