//! Checked, faithful adaptations of Vec::resize upward and Vec::truncate.
//! Allocation failure is outside the stock Vec::push model.
use alloc::vec::Vec;
#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg_attr(creusot, requires(v@.len() <= n@))]
#[cfg_attr(creusot, ensures((^v)@.len() == n@))]
#[cfg_attr(creusot, ensures(forall<i> 0 <= i && i < v@.len() ==> (^v)@[i] == v@[i]))]
#[cfg_attr(creusot, ensures(forall<i> v@.len() <= i && i < n@ ==> (^v)@[i] == 0u8))]
pub fn grow_zero(v: &mut Vec<u8>, n: usize) {
    #[cfg(creusot)]
    let old = snapshot!(v@);
    #[cfg_attr(creusot, invariant(old.len() <= v@.len() && v@.len() <= n@))]
    #[cfg_attr(creusot, invariant(forall<i> 0 <= i && i < old.len() ==> v@[i] == old[i]))]
    #[cfg_attr(creusot, invariant(forall<i> old.len() <= i && i < v@.len() ==> v@[i] == 0u8))]
    while v.len() < n { v.push(0); }
}

#[cfg_attr(creusot, requires(n@ <= v@.len()))]
#[cfg_attr(creusot, ensures((^v)@ == v@.subsequence(0, n@)))]
pub fn truncate(v: &mut Vec<u8>, n: usize) {
    #[cfg(creusot)]
    let old = snapshot!(v@);
    #[cfg_attr(creusot, invariant(n@ <= v@.len() && v@.len() <= old.len()))]
    #[cfg_attr(creusot, invariant(forall<i> 0 <= i && i < v@.len() ==> v@[i] == old[i]))]
    while v.len() > n { v.pop(); }
    #[cfg(creusot)]
    proof_assert!(v@.ext_eq(old.subsequence(0, n@)));
}
