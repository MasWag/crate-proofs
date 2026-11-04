//! Standard UTF-8 encoding boundary and checked structural lemmas.
//! The two character encoding facts below model std, not unindent.
use creusot_std::prelude::*;

#[logic(open)]
pub fn valid(bytes: Seq<u8>) -> bool {
    pearlite! { exists<chars: Seq<char>> chars.to_bytes() == bytes }
}

/// Explicit standard-library assumption, required because frozen CharExt exposes
/// only encoding lengths. Covers every ASCII code point, including NUL/CR/LF.
#[trusted]
#[logic]
#[ensures(forall<c: char> c@ < 128 ==> exists<b: u8>
    b@ == c@ && c.to_utf8() == Seq::singleton(b))]
#[ensures(forall<c: char, i: Int> c@ >= 128 && 0 <= i && i < c.to_utf8().len()
    ==> c.to_utf8()[i]@ >= 128)]
pub fn encoding_laws() {}

extern_spec! {
    impl str {
        #[check(terminates)]
        #[ensures(result@ == self@.to_bytes())]
        fn as_bytes(&self) -> &[u8];
    }
    impl String {
        #[check(terminates)]
        #[ensures(match result {
            Ok(s) => valid(bytes@) && s@.to_bytes() == bytes@,
            Err(_) => !valid(bytes@),
        })]
        fn from_utf8(bytes: Vec<u8>) -> Result<String, std::string::FromUtf8Error>;
    }
}

#[logic]
#[requires(a.len() == b.len())]
#[requires(forall<i: Int> 0 <= i && i < a.len() ==> a[i] == b[i])]
#[ensures(a == b)]
pub fn bytes_extensional<T>(a: Seq<T>, b: Seq<T>) {}

#[logic]
#[requires(s.len() > 0)]
#[ensures(Seq::singleton(s[0]).concat(s.tail()) == s)]
pub fn bytes_head_tail(s: Seq<u8>) {
    let joined = Seq::singleton(s[0]).concat(s.tail());
    proof_assert!(joined[0] == s[0]);
    proof_assert!(forall<i: Int> 1 <= i && i < s.len() ==> s.tail()[i-1] == s[i]);
    proof_assert!(forall<i: Int> 1 <= i && i < s.len() ==> joined[i] == s.tail()[i-1]);
    proof_assert!(forall<i: Int> 0 <= i && i < s.len() ==> joined[i] == s[i]);
    bytes_extensional(joined, s);
}

#[logic]
#[requires(a.len() > 0)]
#[ensures(a.concat(b).tail() == a.tail().concat(b))]
pub fn tail_concat<T>(a: Seq<T>, b: Seq<T>) {
    proof_assert!(forall<i: Int> 0 <= i && i < a.concat(b).tail().len() ==>
        a.concat(b).tail()[i] == a.tail().concat(b)[i]);
    bytes_extensional(a.concat(b).tail(), a.tail().concat(b));
}

#[logic]
#[requires(0 < n && n <= s.len())]
#[ensures(s.subsequence(0, n).tail() == s.tail().subsequence(0, n-1))]
#[ensures(s.tail().subsequence(n-1, s.tail().len()) == s.subsequence(n, s.len()))]
pub fn slice_tail(s: Seq<u8>, n: Int) {
    let a = s.subsequence(0,n).tail();
    let b = s.tail().subsequence(0,n-1);
    proof_assert!(forall<i: Int> 0 <= i && i < a.len() ==> a[i] == b[i]);
    bytes_extensional(a,b);
    let a = s.tail().subsequence(n-1,s.tail().len());
    let b = s.subsequence(n,s.len());
    proof_assert!(forall<i: Int> 0 <= i && i < a.len() ==> a[i] == b[i]);
    bytes_extensional(a,b);
}

#[logic]
#[requires(chars.len() > 0 && chars[0]@ < 128)]
#[ensures(chars.to_bytes().tail() == chars.tail().to_bytes())]
#[ensures(chars[0].to_utf8().len() == 1)]
pub fn ascii_scalar_tail(chars: Seq<char>) {
    encoding_laws();
    proof_assert!(chars[0].to_utf8().len() == 1);
    proof_assert!(forall<i: Int> 0 <= i && i < chars.tail().to_bytes().len() ==> chars.to_bytes().tail()[i] == chars.tail().to_bytes()[i]);
    bytes_extensional(chars.to_bytes().tail(), chars.tail().to_bytes());
}

#[logic]
#[requires(0 <= n && n <= s.len())]
#[ensures(s.subsequence(0, n).concat(s.subsequence(n, s.len())) == s)]
pub fn bytes_split_join(s: Seq<u8>, n: Int) {
    let joined = s.subsequence(0, n).concat(s.subsequence(n, s.len()));
    proof_assert!(forall<i: Int> 0 <= i && i < s.len() ==> joined[i] == s[i]);
    bytes_extensional(joined, s);
}

#[logic]
#[ensures(a.concat(b).to_bytes() == a.to_bytes().concat(b.to_bytes()))]
#[variant(a.len())]
pub fn encoding_concat(a: Seq<char>, b: Seq<char>) {
    if a.len() > 0 {
        encoding_concat(a.tail(), b);
        a[0].to_utf8().concat_assoc(a.tail().to_bytes(), b.to_bytes());
        tail_concat(a, b);
        proof_assert!(a.to_bytes() == a[0].to_utf8().concat(a.tail().to_bytes()));
        proof_assert!(a.concat(b).to_bytes() == a[0].to_utf8().concat(a.concat(b).tail().to_bytes()));
    }
}

#[logic]
#[requires(valid(a) && valid(b))]
#[ensures(valid(a.concat(b)))]
pub fn valid_concat(a: Seq<u8>, b: Seq<u8>) {
    let ca = creusot_std::logic::such_that(|ca: Seq<char>| ca.to_bytes() == a);
    let cb = creusot_std::logic::such_that(|cb: Seq<char>| cb.to_bytes() == b);
    encoding_concat(ca, cb);
}

/// Order-preserving removal of ASCII bytes; no insertion or byte mutation.
#[logic(open)]
#[variant(input.len())]
pub fn ascii_erasure(input: Seq<u8>, output: Seq<u8>) -> bool {
    pearlite! {
        if input.len() == 0 { output.len() == 0 }
        else {
            (input[0]@ < 128 && ascii_erasure(input.tail(), output)) ||
            (output.len() > 0 && input[0] == output[0] && ascii_erasure(input.tail(), output.tail()))
        }
    }
}

#[logic]
#[requires(input.len() > 0 && ascii_erasure(input, output))]
#[requires(input[0]@ >= 128)]
#[ensures(output.len() > 0 && output[0] == input[0])]
#[ensures(ascii_erasure(input.tail(), output.tail()))]
pub fn nonascii_head(input: Seq<u8>, output: Seq<u8>) {}

#[logic]
#[requires(input.len() > 0 && ascii_erasure(input, output))]
#[requires(!ascii_erasure(input.tail(), output))]
#[ensures(output.len() > 0 && output[0] == input[0])]
#[ensures(ascii_erasure(input.tail(), output.tail()))]
pub fn kept_head(input: Seq<u8>, output: Seq<u8>) {}

#[logic]
#[requires(forall<i: Int> 0 <= i && i < a.len() ==> a[i]@ >= 128)]
#[requires(ascii_erasure(a.concat(b), output))]
#[ensures(a.len() <= output.len())]
#[ensures(output.subsequence(0, a.len()) == a)]
#[ensures(ascii_erasure(b, output.subsequence(a.len(), output.len())))]
#[variant(a.len())]
pub fn retained_nonascii_prefix(a: Seq<u8>, b: Seq<u8>, output: Seq<u8>) {
    if a.len() > 0 {
        proof_assert!(a.concat(b).len() > 0);
        proof_assert!(a.concat(b)[0] == a[0]);
        nonascii_head(a.concat(b), output);
        proof_assert!(output[0] == a[0]);
        tail_concat(a, b);
        retained_nonascii_prefix(a.tail(), b, output.tail());
        proof_assert!(a.len() <= output.len());
        slice_tail(output, a.len());
        bytes_head_tail(output.subsequence(0, a.len()));
        bytes_head_tail(a);
        proof_assert!(output.subsequence(0, a.len())[0] == a[0]);
        proof_assert!(output.subsequence(0, a.len()) == a);
    } else {
        proof_assert!(a == Seq::empty());
        proof_assert!(a.concat(b) == b);
        proof_assert!(output.subsequence(0, output.len()) == output);
    }
}

#[logic]
#[requires(ascii_erasure(chars.to_bytes(), output))]
#[ensures(valid(output))]
#[variant(chars.len())]
pub fn encoding_erasure(chars: Seq<char>, output: Seq<u8>) {
    encoding_laws();
    if chars.len() > 0 {
        let first = chars[0];
        Seq::flat_map_singleton(first, |c: char| c.to_utf8());
        proof_assert!(valid(first.to_utf8()));
        if first.view() < 128 {
            ascii_scalar_tail(chars);
            if ascii_erasure(chars.tail().to_bytes(), output) {
                encoding_erasure(chars.tail(), output);
            } else {
                kept_head(chars.to_bytes(), output);
                proof_assert!(output.len() > 0 && output[0] == chars.to_bytes()[0]);
                proof_assert!(first.to_utf8() == Seq::singleton(output[0]));
                encoding_erasure(chars.tail(), output.tail());
                valid_concat(first.to_utf8(), output.tail());
                bytes_head_tail(output);
            }
        } else {
            let width = first.to_utf8().len();
            retained_nonascii_prefix(first.to_utf8(), chars.tail().to_bytes(), output);
            encoding_erasure(chars.tail(), output.subsequence(width, output.len()));
            valid_concat(first.to_utf8(), output.subsequence(width, output.len()));
            bytes_split_join(output, width);
        }
    } else {
        proof_assert!(Seq::<char>::empty().to_bytes() == Seq::<u8>::empty());
        proof_assert!(output == Seq::<u8>::empty());
    }
}

#[logic]
#[requires(valid(input) && ascii_erasure(input, output))]
#[ensures(valid(output))]
pub fn valid_erasure(input: Seq<u8>, output: Seq<u8>) {
    let chars = creusot_std::logic::such_that(|cs: Seq<char>| cs.to_bytes() == input);
    encoding_erasure(chars, output);
}
