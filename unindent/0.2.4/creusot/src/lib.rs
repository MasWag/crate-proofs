pub mod spec;
#[cfg(creusot)]
mod utf8;
#[cfg(creusot)]
mod utf8_trace;
mod lemmas;
use creusot_std::prelude::*;

#[requires(start@ <= s@.len())]
#[ensures(start@ <= result@ && result@ <= s@.len())]
#[ensures(forall<i: Int> start@ <= i && i < result@ ==> s@[i] != 10u8)]
#[ensures(result@ < s@.len() ==> s@[result@] == 10u8)]
#[check(terminates)]
fn line_end_index(s: &[u8], start: usize) -> usize {
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= s@.len())]
    #[invariant(forall<j: Int> start@ <= j && j < i@ ==> s@[j] != 10u8)]
    #[variant(s@.len()-i@)]
    while i < s.len() && s[i] != 10 { i += 1; }
    i
}

#[requires(start@ <= end@ && end@ <= s@.len())]
#[ensures(start@ <= result@ && result@ <= end@)]
#[ensures(forall<i: Int> start@ <= i && i < result@ ==> s@[i] == 32u8 || s@[i] == 9u8)]
#[ensures(result@ < end@ ==> s@[result@] != 32u8 && s@[result@] != 9u8)]
#[check(terminates)]
fn leading_end_index(s: &[u8], start: usize, end: usize) -> usize {
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= end@)]
    #[invariant(forall<j: Int> start@ <= j && j < i@ ==> s@[j] == 32u8 || s@[j] == 9u8)]
    #[variant(end@-i@)]
    while i < end && (s[i] == 32 || s[i] == 9) { i += 1; }
    i
}

#[requires(start@ <= end@ && end@ <= s@.len())]
#[ensures(result@ == initial@.concat(s@.subsequence(start@, end@)))]
#[check(terminates)]
fn append_range(s: &[u8], start: usize, end: usize, initial: Vec<u8>) -> Vec<u8> {
    let mut result = initial;
    let old = snapshot!(result@);
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= end@)]
    #[invariant(result@ == (*old).concat(s@.subsequence(start@, i@)))]
    #[variant(end@-i@)]
    while i < end { result.push(s[i]); i += 1; }
    result
}

#[logic(open)]
pub fn minimum_prefix(s: Seq<u8>, bound: Int, found: bool, margin: Int) -> bool {
    pearlite! { margin >= 0 &&
        (found == exists<a: Int,k: Int> a < bound && spec::later_candidate(s,a,k)) &&
        (!found ==> margin == 0) &&
        (found ==> (exists<a: Int,k: Int> a < bound && spec::later_candidate(s,a,k) && k-a == margin)) &&
        (forall<a: Int,k: Int> a < bound && spec::later_candidate(s,a,k) ==> margin <= k-a) }
}

#[ensures(spec::source_margin(s@,result@))]
#[ensures(minimum_prefix(s@,s@.len()+1, result@ != 0 ||
    (exists<a:Int,k:Int> spec::later_candidate(s@,a,k)),result@))]
#[check(terminates)]
fn common_margin(s: &[u8]) -> usize {
    let mut spaces = 0;
    let mut found_margin = false;
    let mut line_start = line_end_index(s, 0);
    if line_start == s.len() { return 0; }
    line_start += 1;
    #[invariant(line_start@ <= s@.len())]
    #[invariant(0 < line_start@ && s@[line_start@-1] == 10u8)]
    #[invariant(minimum_prefix(s@,line_start@,found_margin,spaces@))]
    #[variant(s@.len()-line_start@)]
    loop {
        let line_end = line_end_index(s, line_start);
        let i = leading_end_index(s, line_start, line_end);
        proof_assert!(forall<a:Int,k:Int> spec::later_candidate(s@,a,k) && line_start@ <= a && a <= line_end@ ==> a == line_start@);
        proof_assert!(forall<k:Int> spec::later_candidate(s@,line_start@,k) ==> k == i@ && i@ < line_end@);
        proof_assert!(i@ < line_end@ ==> spec::later_candidate(s@,line_start@,i@));
        if i < line_end {
            let margin = i - line_start;
            if !found_margin || margin < spaces { spaces = margin; }
            found_margin = true;
        }
        if line_end == s.len() { break; }
        line_start = line_end + 1;
    }
    spaces
}

#[ensures(spec::source_unindented(s@,false,result@))]
#[ensures(result@.len() <= s@.len())]
#[check(terminates)]
pub fn unindent_bytes(s: &[u8]) -> Vec<u8> { do_unindent_bytes(s, false) }

#[ensures(spec::source_unindented(s@,preserve,result@))]
#[ensures(result@.len() <= s@.len())]
#[check(terminates)]
fn do_unindent_bytes(s: &[u8], preserve: bool) -> Vec<u8> {
    let crlf = s.len() >= 2 && s[0] == 13 && s[1] == 10;
    let ignore = !preserve && ((s.len() > 0 && s[0] == 10) || crlf);
    let margin = common_margin(s);
    proof_assert!(spec::source_margin(s@,margin@));
    let mut result = Vec::with_capacity(s.len());
    let mut positions = Seq::<Int>::new();
    let mut i = 0;
    let mut line_start = 0;
    #[invariant(i@ <= s@.len())]
    #[invariant(0 <= line_start@ && line_start@ <= i@)]
    #[invariant(line_start@ == 0 || s@[line_start@-1] == 10u8)]
    #[invariant(forall<j:Int> line_start@ <= j && j < i@ ==> s@[j] != 10u8)]
    #[invariant(spec::selection_trace(s@,margin@,preserve,i@,*positions,result@))]
    #[invariant(result@.len() <= i@)]
    #[variant(s@.len()-i@)]
    while i < s.len() {
        let b = s[i];
        let keep = !(i == 0 && crlf) && if b == 10 {
            !(ignore && (i == 0 || (i == 1 && crlf)))
        } else { line_start == 0 || i - line_start >= margin };
        proof_assert!(spec::source_line_start(s@,line_start@,i@));
        proof_assert!(forall<a:Int> spec::source_line_start(s@,a,i@) ==> a == line_start@);
        proof_assert!(keep == spec::source_keep(s@,margin@,preserve,i@));
        if keep {
            proof_assert!({ lemmas::trace_keep(s@,margin@,preserve,i@,*positions,result@); true });
            result.push(b);
            ghost! {
                let index = snapshot!(i@).into_ghost();
                positions.push_back_ghost(*index);
            };
        } else {
            proof_assert!({ lemmas::trace_skip(s@,margin@,preserve,i@,*positions,result@); true });
        }
        if b == 10 { line_start = i + 1; }
        i += 1;
    }
    proof_assert!(spec::selected_prefix(s@,margin@,preserve,s@.len(),result@));
    result
}

pub trait Unindent {
    type Output;
    fn unindent(&self) -> Self::Output;
}
impl Unindent for [u8] {
    type Output = Vec<u8>;
    #[check(terminates)]
    #[ensures(spec::source_unindented(self@,false,result@))]
    #[ensures(result@.len() <= self@.len())]
    fn unindent(&self) -> Self::Output { unindent_bytes(self) }
}
// The unrestricted extension delegates to arbitrary downstream implementations.
// It has no universal totality/contents contract and is not a selected proof target.
#[cfg(not(creusot))]
impl<T: ?Sized + Unindent> Unindent for &T {
    type Output = T::Output;
    fn unindent(&self) -> Self::Output { (**self).unindent() }
}

#[check(terminates)]
#[ensures(spec::source_unindented(s@.to_bytes(),false,result@.to_bytes()))]
#[ensures(result@.to_bytes().len() <= s@.to_bytes().len())]
pub fn unindent(s: &str) -> String { do_unindent(s,false) }

#[check(terminates)]
#[ensures(spec::source_unindented(s@.to_bytes(),preserve,result@.to_bytes()))]
#[ensures(result@.to_bytes().len() <= s@.to_bytes().len())]
fn do_unindent(s: &str, preserve: bool) -> String {
    let bytes = s.as_bytes();
    let out = do_unindent_bytes(bytes,preserve);
    proof_assert!({ utf8_trace::source_erasure(bytes@,preserve,out@); true });
    proof_assert!(utf8::valid(bytes@));
    proof_assert!({ utf8::valid_erasure(bytes@,out@); true });
    String::from_utf8(out).unwrap()
}

impl Unindent for str {
    type Output = String;
    #[check(terminates)]
    #[ensures(spec::source_unindented(self@.to_bytes(),false,result@.to_bytes()))]
    #[ensures(result@.to_bytes().len() <= self@.to_bytes().len())]
    fn unindent(&self) -> Self::Output { unindent(self) }
}
impl Unindent for String {
    type Output = String;
    #[check(terminates)]
    #[ensures(spec::source_unindented(self@.to_bytes(),false,result@.to_bytes()))]
    #[ensures(result@.to_bytes().len() <= self@.to_bytes().len())]
    fn unindent(&self) -> Self::Output { unindent(self) }
}

#[cfg(test)]
#[path = "../../.work/source/src/unindent.rs"]
mod native_release;
#[cfg(test)]
mod flag_tests {
    #[test]
    fn preserve_flag_differential() {
        let alphabet = ['\0','\t','\n','\r',' ','A','é','🦀'];
        let mut cases = 0;
        for len in 0..=5 {
            for mut code in 0..alphabet.len().pow(len as u32) {
                let mut input = String::new();
                for _ in 0..len { input.push(alphabet[code % alphabet.len()]); code /= alphabet.len(); }
                for preserve in [false,true] {
                    let expected = super::native_release::do_unindent(&input,preserve);
                    assert_eq!(super::do_unindent(&input,preserve),expected,"{input:?}, preserve={preserve}");
                    assert_eq!(super::do_unindent_bytes(input.as_bytes(),preserve),expected.as_bytes());
                    cases += 1;
                }
            }
        }
        println!("native flagged string/bytes cases={cases}");
    }
}
