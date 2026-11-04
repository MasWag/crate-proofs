use creusot_std::prelude::*;
use crate::spec::*;

#[logic]
#[requires(selection_trace(s,m,p,bound,positions,out))]
#[requires(bound < s.len())]
#[requires(source_keep(s,m,p,bound))]
#[ensures(selection_trace(s,m,p,bound+1,positions.push_back(bound),out.push_back(s[bound])))]
pub fn trace_keep(s:Seq<u8>,m:Int,p:bool,bound:Int,positions:Seq<Int>,out:Seq<u8>) {}

#[logic]
#[requires(selection_trace(s,m,p,bound,positions,out))]
#[requires(bound < s.len())]
#[requires(!source_keep(s,m,p,bound))]
#[ensures(selection_trace(s,m,p,bound+1,positions,out))]
pub fn trace_skip(s:Seq<u8>,m:Int,p:bool,bound:Int,positions:Seq<Int>,out:Seq<u8>) {}

#[logic]
#[requires(0 < a && a <= at && at <= end && end < s.len())]
#[requires(s[a-1] == 10u8)]
#[requires(forall<j:Int> a <= j && j < at ==> white(s[j]))]
#[requires(forall<j:Int> a <= j && j <= end ==> s[j] != 10u8)]
#[requires(!white(s[end]))]
#[ensures(later_candidate(s,a,result))]
#[ensures(a <= result && result <= end)]
#[variant(end-at)]
pub fn first_nonwhite(s:Seq<u8>,a:Int,at:Int,end:Int) -> Int {
    pearlite! { if white(s[at]) { first_nonwhite(s,a,at+1,end) } else { at } }
}

#[logic]
#[requires(0 <= at && at <= i && i < s.len())]
#[requires(forall<j:Int> at <= j && j < i ==> s[j] != 10u8)]
#[ensures(source_line_start(s,result,i))]
#[variant(at)]
pub fn find_start(s:Seq<u8>,i:Int,at:Int) -> Int {
    pearlite! { if at == 0 || s[at-1] == 10u8 { at } else { find_start(s,i,at-1) } }
}

#[logic]
#[requires(source_margin(s,m))]
#[requires(0 <= i && i < s.len())]
#[requires(s[i]@ >= 128)]
#[ensures(source_keep(s,m,p,i))]
pub fn nonascii_kept(s:Seq<u8>,m:Int,p:bool,i:Int) {
    pearlite! {
        let a = find_start(s,i,i);
        if a > 0 { let k = first_nonwhite(s,a,a,i); }
    }
}
