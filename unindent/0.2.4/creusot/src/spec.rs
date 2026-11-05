//! Independent declarative specification. No application proof is assumed here.
use creusot_std::prelude::*;

#[logic(open)]
pub fn white(b: u8) -> bool { b == 32u8 || b == 9u8 }

#[logic(open)]
pub fn blank(line: Seq<u8>) -> bool {
    pearlite! { forall<i: Int> 0 <= i && i < line.len() ==> white(line[i]) }
}

#[logic(open)]
pub fn indentation(line: Seq<u8>, k: Int) -> bool {
    pearlite! { 0 <= k && k < line.len() && !white(line[k]) &&
        (forall<i: Int> 0 <= i && i < k ==> white(line[i])) }
}

#[logic(open)]
pub fn initial_crlf(s: Seq<u8>) -> bool {
    pearlite! { s.len() >= 2 && s[0] == 13u8 && s[1] == 10u8 }
}

#[logic(open)]
pub fn prepare(s: Seq<u8>) -> Seq<u8> {
    pearlite! { if initial_crlf(s) { s.subsequence(1, s.len()) } else { s } }
}

#[logic(open)]
pub fn ignore_first(s: Seq<u8>, preserve: bool) -> bool {
    pearlite! { !preserve && ((s.len() > 0 && s[0] == 10u8) || initial_crlf(s)) }
}

/// LF intercalation, including all empty fields. Defined for empty lists too.
#[logic(open)]
pub fn intercalate(lines: Seq<Seq<u8>>) -> Seq<u8> {
    pearlite! {
        Seq::create(lines.len(), |i: Int|
            if i == 0 { lines[i] } else { Seq::singleton(10u8).concat(lines[i]) }
        ).flatten()
    }
}

#[logic(open)]
pub fn decomposition(s: Seq<u8>, lines: Seq<Seq<u8>>) -> bool {
    pearlite! { lines.len() > 0 && intercalate(lines) == s &&
        (forall<i: Int, j: Int> 0 <= i && i < lines.len() &&
            0 <= j && j < lines[i].len() ==> lines[i][j] != 10u8) }
}

#[logic(open)]
pub fn eligible(lines: Seq<Seq<u8>>, k: Int) -> bool {
    pearlite! { exists<i: Int> 1 <= i && i < lines.len() && indentation(lines[i], k) }
}

/// Exact minimum: attainment matters; a mere lower bound is insufficient.
#[logic(open)]
pub fn margin(lines: Seq<Seq<u8>>, m: Int) -> bool {
    pearlite! { 0 <= m &&
        ((m == 0 && (forall<k: Int> !eligible(lines, k))) ||
         (eligible(lines, m) && (forall<k: Int> eligible(lines, k) ==> m <= k))) }
}

#[logic(open)]
pub fn drop_prefix(line: Seq<u8>, m: Int) -> Seq<u8> {
    pearlite! {
        if m <= 0 { line }
        else if m >= line.len() { Seq::empty() }
        else { line.subsequence(m, line.len()) }
    }
}

#[logic(open)]
pub fn transformed(lines: Seq<Seq<u8>>, m: Int) -> Seq<Seq<u8>> {
    pearlite! { Seq::create(lines.len(), |i: Int|
        if i == 0 { lines[i] } else { drop_prefix(lines[i], m) }) }
}

#[logic(open)]
pub fn rendered(lines: Seq<Seq<u8>>, m: Int, ignore: bool) -> Seq<u8> {
    pearlite! {
        let ts = transformed(lines, m);
        intercalate(if ignore && ts.len() > 0 { ts.subsequence(1, ts.len()) } else { ts })
    }
}

/// Exact public/private contents relation; preserve=false is the public API.
#[logic(open)]
pub fn unindented(s: Seq<u8>, preserve: bool, out: Seq<u8>) -> bool {
    pearlite! { exists<lines: Seq<Seq<u8>>, m: Int>
        decomposition(prepare(s), lines) && margin(lines, m) &&
        out == rendered(lines, m, ignore_first(s, preserve)) }
}

/// Quantifier-based original-source later-line candidate, for scanner bridges.
/// This is independent of any operational loop or recursive scanner.
#[logic(open)]
pub fn later_candidate(s: Seq<u8>, a: Int, k: Int) -> bool {
    pearlite! { 0 < a && a <= k && k < s.len() && s[a - 1] == 10u8 &&
        s[k] != 10u8 && !white(s[k]) &&
        (forall<j: Int> a <= j && j < k ==> white(s[j])) }
}

#[logic(open)]
pub fn source_margin(s: Seq<u8>, m: Int) -> bool {
    pearlite! { 0 <= m &&
        ((m == 0 && (forall<a: Int, k: Int> !later_candidate(s, a, k))) ||
         ((exists<a: Int, k: Int> later_candidate(s, a, k) && m == k - a) &&
          (forall<a: Int, k: Int> later_candidate(s, a, k) ==> m <= k - a))) }
}

#[logic(open)]
pub fn source_line_start(s: Seq<u8>, a: Int, i: Int) -> bool {
    pearlite! { 0 <= a && a <= i && i < s.len() &&
        (a == 0 || s[a - 1] == 10u8) &&
        (forall<j: Int> a <= j && j < i ==> s[j] != 10u8) }
}

/// Independent retained-source-position characterization.
/// Equivalence with `unindented` is a separate checked bridge obligation.
#[logic(open)]
pub fn source_keep(s: Seq<u8>, m: Int, preserve: bool, i: Int) -> bool {
    pearlite! { 0 <= i && i < s.len() &&
        !(i == 0 && initial_crlf(s)) &&
        (if s[i] == 10u8 {
            !(ignore_first(s, preserve) &&
                (i == 0 || (i == 1 && initial_crlf(s))))
        } else {
            exists<a: Int> source_line_start(s, a, i) && (a == 0 || m <= i - a)
        }) }
}

/// Explicit ordered source trace, useful as a loop witness.
/// Completeness prevents a shorter output from satisfying a mere subsequence law.
#[logic(open)]
pub fn selection_trace(
    s: Seq<u8>, m: Int, preserve: bool, bound: Int,
    positions: Seq<Int>, out: Seq<u8>,
) -> bool {
    pearlite! { 0 <= bound && bound <= s.len() && out.len() == positions.len() &&
        (forall<j: Int> 0 <= j && j < positions.len() ==>
            0 <= positions[j] && positions[j] < bound &&
            source_keep(s, m, preserve, positions[j]) && out[j] == s[positions[j]]) &&
        (forall<j: Int, k: Int> 0 <= j && j < k && k < positions.len() ==>
            positions[j] < positions[k]) &&
        (forall<i: Int> 0 <= i && i < bound && source_keep(s, m, preserve, i) ==>
            exists<j: Int> 0 <= j && j < positions.len() && positions[j] == i) }
}

#[logic(open)]
pub fn selected_prefix(s: Seq<u8>, m: Int, preserve: bool, bound: Int, out: Seq<u8>) -> bool {
    pearlite! { exists<positions: Seq<Int>> selection_trace(s, m, preserve, bound, positions, out) }
}

/// Full source-position semantics; not yet a theorem connecting to decomposition U.
#[logic(open)]
pub fn source_unindented(s: Seq<u8>, preserve: bool, out: Seq<u8>) -> bool {
    pearlite! { exists<m: Int> source_margin(s, m) && selected_prefix(s, m, preserve, s.len(), out) }
}
