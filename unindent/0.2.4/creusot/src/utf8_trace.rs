//! Checked bridge from a complete ordered source-position trace to ASCII erasure.
use creusot_std::prelude::*;
use crate::utf8::ascii_erasure;

#[logic]
#[requires(positions.len() > 0 && positions[0] == start)]
#[requires(forall<i: Int> start < i && i < source.len() && source[i]@ >= 128 ==>
    exists<k: Int> 1 <= k && k < positions.len() && positions[k] == i)]
#[ensures(forall<i: Int> start < i && i < source.len() && source[i]@ >= 128 ==>
    exists<k: Int> 0 <= k && k < positions.tail().len() && positions.tail()[k] == i)]
pub fn tail_complete(source: Seq<u8>, start: Int, positions: Seq<Int>) {
    pearlite! {
        if exists<i: Int> start < i && i < source.len() && source[i]@ >= 128 &&
            !(exists<k: Int> 0 <= k && k < positions.tail().len() && positions.tail()[k] == i) {
            let i = creusot_std::logic::such_that(|i: Int| start < i && i < source.len() && source[i]@ >= 128 &&
                !(exists<k: Int> 0 <= k && k < positions.tail().len() && positions.tail()[k] == i));
            let k = creusot_std::logic::such_that(|k: Int| 1 <= k && k < positions.len() && positions[k] == i);
            proof_assert!(0 <= k - 1 && k - 1 < positions.tail().len() && positions.tail()[k-1] == i);
        }
    }
}

#[logic]
#[requires(0 <= start && start <= source.len())]
#[requires(positions.len() == output.len())]
#[requires(forall<k: Int> 0 <= k && k < positions.len() ==>
    start <= positions[k] && positions[k] < source.len() && output[k] == source[positions[k]])]
#[requires(forall<k: Int, l: Int> 0 <= k && k < l && l < positions.len() ==> positions[k] < positions[l])]
#[requires(forall<i: Int> start <= i && i < source.len() && source[i]@ >= 128 ==>
    exists<k: Int> 0 <= k && k < positions.len() && positions[k] == i)]
#[ensures(ascii_erasure(source.subsequence(start, source.len()), output))]
#[variant(source.len() - start)]
pub fn trace_erasure(source: Seq<u8>, start: Int, positions: Seq<Int>, output: Seq<u8>) {
    if start < source.len() {
        proof_assert!(source.subsequence(start, source.len()).tail() == source.subsequence(start + 1, source.len()));
        if positions.len() > 0 && positions[0] == start {
            proof_assert!(forall<k: Int> 1 <= k && k < positions.len() ==> positions[k] > start);
            proof_assert!(forall<i: Int> start + 1 <= i && i < source.len() && source[i]@ >= 128 ==>
                exists<k: Int> 1 <= k && k < positions.len() && positions[k] == i);
            tail_complete(source, start, positions);
            trace_erasure(source, start + 1, positions.tail(), output.tail());
        } else {
            proof_assert!(forall<k: Int> 0 <= k && k < positions.len() ==> positions[k] != start);
            proof_assert!(source[start]@ < 128);
            trace_erasure(source, start + 1, positions, output);
        }
    }
}

#[logic]
#[requires(crate::spec::source_margin(source, margin))]
#[ensures(forall<i: Int> 0 <= i && i < source.len() && source[i]@ >= 128 ==>
    crate::spec::source_keep(source, margin, preserve, i))]
pub fn all_nonascii_kept(source: Seq<u8>, margin: Int, preserve: bool) {
    pearlite! {
        if exists<i: Int> 0 <= i && i < source.len() && source[i]@ >= 128 &&
            !crate::spec::source_keep(source, margin, preserve, i) {
            let i = creusot_std::logic::such_that(|i: Int| 0 <= i && i < source.len() &&
                source[i]@ >= 128 && !crate::spec::source_keep(source, margin, preserve, i));
            crate::lemmas::nonascii_kept(source, margin, preserve, i);
        }
    }
}

#[logic]
#[requires(crate::spec::source_unindented(source, preserve, output))]
#[ensures(ascii_erasure(source, output))]
pub fn source_erasure(source: Seq<u8>, preserve: bool, output: Seq<u8>) {
    let margin = creusot_std::logic::such_that(|m: Int|
        crate::spec::source_margin(source, m) &&
        crate::spec::selected_prefix(source, m, preserve, source.len(), output));
    let positions = creusot_std::logic::such_that(|p: Seq<Int>|
        crate::spec::selection_trace(source, margin, preserve, source.len(), p, output));
    all_nonascii_kept(source, margin, preserve);
    trace_erasure(source, 0, positions, output);
    proof_assert!(source.subsequence(0, source.len()) == source);
}
