//! Checked uniqueness of positional notation, including leading zero symbols.
use creusot_std::prelude::*;
use crate::spec;

#[logic(open)]
#[variant(a.len())]
pub fn value(a: Seq<Int>, radix: Int) -> Int {
    pearlite! { if a.len() == 0 { 0 } else {
        radix * value(a.subsequence(0, a.len()-1), radix) + a[a.len()-1]
    } }
}

#[logic(open)]
#[variant(a.len())]
pub fn zeros(a: Seq<Int>) -> Int {
    pearlite! { if a.len() == 0 || a[0] != 0 { 0 }
        else { 1 + zeros(a.subsequence(1, a.len())) } }
}

#[logic(opaque)]
#[requires(radix >= 2)]
#[requires(forall<i: Int> 0 <= i && i < a.len() ==> 0 <= a[i] && a[i] < radix)]
#[variant(a.len())]
#[ensures(result && 0 <= value(a, radix) && 0 <= zeros(a) && zeros(a) <= a.len())]
#[ensures(result && (value(a, radix) == 0) == (zeros(a) == a.len()))]
#[ensures(result && (value(a, radix) == 0 ==> forall<i: Int> 0 <= i && i < a.len() ==> a[i] == 0))]
pub fn zero_value(a: Seq<Int>, radix: Int) -> bool {
    pearlite! { if a.len() == 0 {
        value(a, radix) == 0 && zeros(a) == 0
    } else {
        zero_value(a.subsequence(0, a.len()-1), radix)
        && zeros_last(a)
        && (forall<i: Int> 0 <= i && i < a.len()-1 ==> a.subsequence(0,a.len()-1)[i] == a[i])
        && (value(a, radix) == 0 ==> forall<i: Int> 0 <= i && i < a.len() ==> a[i] == 0)
        && 0 <= value(a, radix) && 0 <= zeros(a) && zeros(a) <= a.len()
        && ((value(a, radix) == 0) == (zeros(a) == a.len()))
    } }
}

#[logic(opaque)]
#[requires(a.len() > 0)]
#[variant(a.len())]
#[ensures(result && zeros(a) == if zeros(a.subsequence(0,a.len()-1)) == a.len()-1 && a[a.len()-1] == 0 { a.len() } else { zeros(a.subsequence(0,a.len()-1)) })]
pub fn zeros_last(a: Seq<Int>) -> bool {
    pearlite! { if a.len() == 1 {
        a.subsequence(0,0).len() == 0 && a.subsequence(1,1).len() == 0
        && zeros(a) == if a[0] == 0 { 1 } else { 0 }
    } else {
        zeros_last(a.subsequence(1,a.len()))
        && a.subsequence(0,a.len()-1)[0] == a[0]
        && a.subsequence(0,a.len()-1).subsequence(1,a.len()-1)
            == a.subsequence(1,a.len()).subsequence(0,a.len()-2)
        && a.subsequence(1,a.len())[a.len()-2] == a[a.len()-1]
        && zeros(a) == if zeros(a.subsequence(0,a.len()-1)) == a.len()-1 && a[a.len()-1] == 0 { a.len() } else { zeros(a.subsequence(0,a.len()-1)) }
    } }
}

#[logic(opaque)]
#[requires(radix >= 2 && 0 <= x && x < radix && 0 <= y && y < radix)]
#[requires(radix * p + x == radix * q + y)]
#[ensures(result && p == q && x == y)]
pub fn positional_step(radix: Int, p: Int, q: Int, x: Int, y: Int) -> bool {
    pearlite! { p == q && x == y }
}

#[logic(opaque)]
#[requires(radix >= 2)]
#[requires(forall<i: Int> 0 <= i && i < a.len() ==> 0 <= a[i] && a[i] < radix)]
#[requires(forall<i: Int> 0 <= i && i < b.len() ==> 0 <= b[i] && b[i] < radix)]
#[requires(value(a,radix) == value(b,radix) && zeros(a) == zeros(b))]
#[variant(a.len()+b.len())]
#[ensures(result && a == b)]
pub fn unique(a: Seq<Int>, b: Seq<Int>, radix: Int) -> bool {
    pearlite! {
        zero_value(a,radix) && zero_value(b,radix)
        && if value(a,radix) == 0 {
            a.len() == b.len()
            && (forall<i: Int> 0 <= i && i < a.len() ==> a[i] == b[i])
            && a == b
        } else {
            a.len() > 0 && b.len() > 0
            && positional_step(radix, value(a.subsequence(0,a.len()-1),radix),
                value(b.subsequence(0,b.len()-1),radix), a[a.len()-1], b[b.len()-1])
            && zero_value(a.subsequence(0,a.len()-1),radix)
            && zero_value(b.subsequence(0,b.len()-1),radix)
            && zeros_last(a) && zeros_last(b)
            && zeros(a.subsequence(0,a.len()-1)) == zeros(b.subsequence(0,b.len()-1))
            && unique(a.subsequence(0,a.len()-1),b.subsequence(0,b.len()-1),radix)
            && a.len() == b.len()
            && (forall<i: Int> 0 <= i && i < a.len()-1 ==>
                a[i] == a.subsequence(0,a.len()-1)[i]
                && b[i] == b.subsequence(0,b.len()-1)[i]
                && a[i] == b[i])
            && (forall<i: Int> 0 <= i && i < a.len() ==> a[i] == b[i])
            && a == b
        }
    }
}

#[logic(open)]
pub fn bytes(a: Seq<u8>) -> Seq<Int> { pearlite! { Seq::create(a.len(), |i: Int| a[i]@) } }

#[logic(open)]
pub fn symbols(a: Seq<u8>, decode: Seq<u8>) -> Seq<Int> {
    pearlite! { Seq::create(a.len(), |i: Int| spec::digit(decode,a[i])) }
}

#[logic(opaque)]
#[variant(a.len())]
#[ensures(result && value(bytes(a),256) == spec::be(a,256) && zeros(bytes(a)) == spec::leading(a,0u8))]
pub fn byte_bridge(a: Seq<u8>) -> bool {
    pearlite! { if a.len() == 0 {
        value(bytes(a),256) == spec::be(a,256) && zeros(bytes(a)) == spec::leading(a,0u8)
    } else {
        bytes(a).subsequence(0,a.len()-1) == bytes(a.subsequence(0,a.len()-1))
        && bytes(a).subsequence(1,a.len()) == bytes(a.subsequence(1,a.len()))
        && byte_bridge(a.subsequence(0,a.len()-1))
        && byte_bridge(a.subsequence(1,a.len()))
        && value(bytes(a),256) == spec::be(a,256) && zeros(bytes(a)) == spec::leading(a,0u8)
    } }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode) && spec::good_prefix(a,decode,a.len()))]
#[variant(a.len())]
#[ensures(result && value(symbols(a,decode),58) == spec::be58(a,decode))]
#[ensures(result && zeros(symbols(a,decode)) == spec::leading(a,encode[0]))]
pub fn symbol_bridge(a: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! { if a.len() == 0 {
        value(symbols(a,decode),58) == spec::be58(a,decode)
        && zeros(symbols(a,decode)) == spec::leading(a,encode[0])
    } else {
        symbols(a,decode).subsequence(0,a.len()-1) == symbols(a.subsequence(0,a.len()-1),decode)
        && symbols(a,decode).subsequence(1,a.len()) == symbols(a.subsequence(1,a.len()),decode)
        && symbol_bridge(a.subsequence(0,a.len()-1),encode,decode)
        && symbol_bridge(a.subsequence(1,a.len()),encode,decode)
        && ((spec::digit(decode,a[0]) == 0) == (a[0] == encode[0]))
        && value(symbols(a,decode),58) == spec::be58(a,decode)
        && zeros(symbols(a,decode)) == spec::leading(a,encode[0])
    } }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode))]
#[requires(spec::encoded(input,text,encode,decode) && spec::decoded(text,output,encode,decode))]
#[ensures(result && input == output)]
pub fn decode_encode(input: Seq<u8>, text: Seq<u8>, output: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! { byte_bridge(input) && byte_bridge(output)
        && unique(bytes(input),bytes(output),256)
        && input == output }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode))]
#[requires(spec::decoded(text,input,encode,decode) && spec::encoded(input,output,encode,decode))]
#[ensures(result && text == output)]
pub fn encode_decode(text: Seq<u8>, input: Seq<u8>, output: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! { symbol_bridge(text,encode,decode) && symbol_bridge(output,encode,decode)
        && unique(symbols(text,decode),symbols(output,decode),58)
        && (forall<i: Int> 0 <= i && i < text.len() ==> text[i] == output[i])
        && text == output }
}

#[logic(opaque)]
#[requires(radix >= 2 && p < q && 0 <= digit && digit < radix)]
#[ensures(result && radix*p+digit < radix*q)]
pub fn horner_bound(radix: Int, p: Int, q: Int, digit: Int) -> bool {
    pearlite! { p <= q-1 && radix*p <= radix*(q-1)
        && radix*(q-1) == radix*q-radix && radix*p+digit < radix*q }
}

#[logic(opaque)]
#[requires(0 <= a && a <= b && 0 <= x && x <= y)]
#[ensures(result && a*x <= b*y)]
pub fn product_monotone(a: Int, b: Int, x: Int, y: Int) -> bool {
    pearlite! { a*x <= b*x && b*x <= b*y && a*x <= b*y }
}

/// Positional magnitude needs only the digits following the leading zeros.
#[logic(opaque)]
#[requires(radix >= 2)]
#[requires(forall<i: Int> 0 <= i && i < a.len() ==> 0 <= a[i] && a[i] < radix)]
#[variant(a.len())]
#[ensures(result && value(a,radix) < spec::pow(radix,a.len()-zeros(a)))]
pub fn magnitude_bound(a: Seq<Int>, radix: Int) -> bool {
    pearlite! {
        zero_value(a,radix)
        && if a.len() == 0 {
            value(a,radix) < spec::pow(radix,a.len()-zeros(a))
        } else {
            magnitude_bound(a.subsequence(0,a.len()-1),radix)
            && zero_value(a.subsequence(0,a.len()-1),radix)
            && zeros_last(a)
            && spec::pow_positive(radix,a.len()-1-zeros(a.subsequence(0,a.len()-1)))
            && if zeros(a) == a.len() {
                value(a,radix) < spec::pow(radix,a.len()-zeros(a))
            } else {
                zeros(a) == zeros(a.subsequence(0,a.len()-1))
                && spec::pow(radix,a.len()-zeros(a))
                    == radix * spec::pow(radix,a.len()-1-zeros(a.subsequence(0,a.len()-1)))
                && horner_bound(radix,value(a.subsequence(0,a.len()-1),radix),
                    spec::pow(radix,a.len()-1-zeros(a.subsequence(0,a.len()-1))),a[a.len()-1])
                && value(a,radix) < spec::pow(radix,a.len()-zeros(a))
            }
        }
    }
}

#[logic(opaque)]
#[requires(0 <= n && 2 <= a && a <= b)]
#[variant(n)]
#[ensures(result && spec::pow(a,n) <= spec::pow(b,n))]
pub fn radix_monotone(a: Int, b: Int, n: Int) -> bool {
    pearlite! { if n == 0 { spec::pow(a,n) <= spec::pow(b,n) }
        else { radix_monotone(a,b,n-1) && spec::pow_positive(a,n-1)
            && spec::pow_positive(b,n-1)
            && product_monotone(a,b,spec::pow(a,n-1),spec::pow(b,n-1))
            && spec::pow(a,n) <= spec::pow(b,n) } }
}

#[logic(opaque)]
#[requires(n >= 0)]
#[variant(n)]
#[ensures(result && spec::pow(256,n) <= spec::pow(58,n+(n+1)/2))]
pub fn encode_power(n: Int) -> bool {
    pearlite! { if n < 2 {
        spec::pow(256,n) <= spec::pow(58,n+(n+1)/2)
    } else {
        encode_power(n-2)
        && spec::pow_positive(58,(n-2)+(n-1)/2)
        && n+(n+1)/2 == (n-2)+(n-1)/2+3
        && spec::pow(256,n) == 65536 * spec::pow(256,n-2)
        && spec::pow(58,n+(n+1)/2) == 195112 * spec::pow(58,(n-2)+(n-1)/2)
        && spec::pow(256,n) <= spec::pow(58,n+(n+1)/2)
    } }
}

#[logic(opaque)]
#[ensures(result && spec::encode_fits(input,input.len()+(input.len()+1)/2))]
pub fn encode_capacity(input: Seq<u8>) -> bool {
    pearlite! { byte_bridge(input) && zero_value(bytes(input),256)
        && magnitude_bound(bytes(input),256)
        && encode_power(input.len()-spec::leading(input,0u8))
        && crate::lemmas::pow_monotone(58,
            input.len()-spec::leading(input,0u8)+(input.len()-spec::leading(input,0u8)+1)/2,
            input.len()+(input.len()+1)/2-spec::leading(input,0u8))
        && spec::encode_fits(input,input.len()+(input.len()+1)/2) }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode) && spec::good_prefix(input,decode,input.len()))]
#[ensures(result && spec::decode_fits(input,encode,decode,input.len()))]
pub fn decode_capacity(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! { symbol_bridge(input,encode,decode)
        && zero_value(symbols(input,decode),58)
        && magnitude_bound(symbols(input,decode),58)
        && radix_monotone(58,256,input.len()-spec::leading(input,encode[0]))
        && spec::decode_fits(input,encode,decode,input.len()) }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode) && spec::decode_fits(input,encode,decode,capacity))]
#[requires(0 <= n && n <= input.len())]
#[ensures(result && spec::be58(input.subsequence(0,n),decode) < spec::pow(256,capacity))]
pub fn decode_prefix_fits(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>, capacity: Int, n: Int) -> bool {
    pearlite! { crate::encoder_lemmas::leading_bounds(input,encode[0])
        && crate::lemmas::be58_prefix_monotone(input,decode,n,input.len())
        && input.subsequence(0,input.len()) == input
        && crate::lemmas::pow_monotone(256,capacity-spec::leading(input,encode[0]),capacity)
        && spec::be58(input.subsequence(0,n),decode) < spec::pow(256,capacity) }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode) && spec::decode_fits(input,encode,decode,capacity))]
#[ensures(result && !spec::decode_error(input,encode,decode,capacity,error))]
pub fn decode_error_excluded(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>, capacity: Int, error: crate::DecodeError) -> bool {
    pearlite! { (forall<n: Int> 0 <= n && n <= input.len() ==>
            decode_prefix_fits(input,encode,decode,capacity,n)
            && spec::be58(input.subsequence(0,n),decode) < spec::pow(256,capacity))
        && !spec::decode_error(input,encode,decode,capacity,error) }
}

/// Even a valid prefix of an otherwise invalid string cannot exhaust the
/// decoder's one-byte-per-input-symbol allocation.
#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode))]
#[requires(0 <= n && n <= input.len() && spec::good_prefix(input,decode,n))]
#[ensures(result && spec::be58(input.subsequence(0,n),decode) < spec::pow(256,input.len()))]
pub fn valid_prefix_capacity(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>, n: Int) -> bool {
    pearlite! { spec::good_prefix(input.subsequence(0,n),decode,n)
        && decode_capacity(input.subsequence(0,n),encode,decode)
        && decode_prefix_fits(input.subsequence(0,n),encode,decode,n,n)
        && input.subsequence(0,n).subsequence(0,n) == input.subsequence(0,n)
        && crate::lemmas::pow_monotone(256,n,input.len())
        && spec::be58(input.subsequence(0,n),decode) < spec::pow(256,input.len()) }
}

#[logic(opaque)]
#[requires(spec::valid_alphabet(encode,decode))]
#[ensures(result && !spec::decode_error(input,encode,decode,input.len(),crate::DecodeError::BufferTooSmall))]
pub fn decode_no_buffer_error(input: Seq<u8>, encode: Seq<u8>, decode: Seq<u8>) -> bool {
    pearlite! { (forall<n: Int> 0 <= n && n <= input.len() && spec::good_prefix(input,decode,n) ==>
            valid_prefix_capacity(input,encode,decode,n)
            && spec::be58(input.subsequence(0,n),decode) < spec::pow(256,input.len()))
        && (spec::good_prefix(input,decode,input.len()) ==> decode_capacity(input,encode,decode)
            && spec::decode_fits(input,encode,decode,input.len()))
        && !spec::decode_error(input,encode,decode,input.len(),crate::DecodeError::BufferTooSmall) }
}
