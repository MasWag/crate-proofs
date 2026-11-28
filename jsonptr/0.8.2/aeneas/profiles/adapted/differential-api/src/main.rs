//! Differential comparison of jsonptr 0.8.2 release APIs with the adapted
//! extension bodies (`jsonptr::adapted_api`) of the Aeneas `adapted` profile.
//!
//! Inputs are enumerated exhaustively over `ALPHABET` up to stated lengths.
//! Complete results are compared, including every error field, final buffers
//! after mutation, and panics (caught with `catch_unwind`). Agreement is
//! evidence for the release-correspondence obligations, not a proof.

mod tier4;
use jsonptr::adapted_api as a;
use jsonptr::adapted_api::{BoundAdapted, ComponentAdapted};
use jsonptr::diagnostic::{Diagnostic, Label};
use jsonptr::index::Index;
use jsonptr::{Component, EncodingError, ParseError, Pointer, PointerBuf, ReplaceError, Token};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::ops::Bound;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::str::FromStr;

const ALPHABET: [char; 11] = ['/', '~', '0', '1', '2', '9', '-', '+', 'a', '\0', 'é'];
/// Single-pointer operations and parse wrappers: every string up to this many characters.
const MAX_LEN: usize = 6;
/// Pointer pairs (prefix/suffix/intersection/append/order/equality): both up to this length.
const PAIR_LEN: usize = 4;
/// Token arguments of mutations: every valid encoded token up to this length.
const TOKEN_LEN: usize = 2;

#[derive(Default)]
struct Counts(BTreeMap<&'static str, u64>);
impl Counts {
    fn add(&mut self, k: &'static str) {
        *self.0.entry(k).or_default() += 1;
    }
}

fn strings(max_len: usize) -> Vec<String> {
    let mut out = vec![String::new()];
    let mut layer = vec![String::new()];
    for _ in 0..max_len {
        let mut next = Vec::new();
        for s in &layer {
            for c in ALPHABET {
                let mut t = s.clone();
                t.push(c);
                next.push(t);
            }
        }
        out.extend(next.iter().cloned());
        layer = next;
    }
    out
}

fn caught<T>(f: impl FnOnce() -> T) -> Result<T, ()> {
    catch_unwind(AssertUnwindSafe(f)).map_err(|_| ())
}

fn b(s: &str) -> &[u8] {
    s.as_bytes()
}

fn ptr_bytes(p: Option<&Pointer>) -> Option<Vec<u8>> {
    p.map(|p| p.as_str().as_bytes().to_vec())
}

fn tok_bytes(t: Option<Token<'_>>) -> Option<Vec<u8>> {
    t.map(|t| t.encoded().as_bytes().to_vec())
}

fn opt_vec(o: Option<&[u8]>) -> Option<Vec<u8>> {
    o.map(|s| s.to_vec())
}

macro_rules! check {
    ($c:expr, $key:literal, $lhs:expr, $rhs:expr, $ctx:expr) => {{
        let l = $lhs;
        let r = $rhs;
        if l != r {
            panic!("MISMATCH {} on {:?}: release {:?} vs adapted {:?}", $key, $ctx, l, r);
        }
        $c.add($key);
    }};
}

fn main() {
    std::panic::set_hook(Box::new(|info| {
        let msg = info.to_string();
        if msg.contains("MISMATCH") {
            eprintln!("{msg}");
        }
    }));
    let mut c = Counts::default();
    let all = strings(MAX_LEN);
    let pointers: Vec<&str> = all.iter().map(|s| s.as_str()).filter(|s| Pointer::parse(s).is_ok()).collect();
    let small: Vec<&str> = pointers.iter().copied().filter(|s| s.chars().count() <= PAIR_LEN).collect();
    let tokens: Vec<String> = strings(TOKEN_LEN).into_iter().filter(|s| Token::from_encoded(s.as_str()).is_ok()).collect();
    println!(
        "inputs: {} strings (<= {MAX_LEN} chars), {} valid pointers, {} pair pointers (<= {PAIR_LEN}), {} tokens (<= {TOKEN_LEN})",
        all.len(),
        pointers.len(),
        small.len(),
        tokens.len()
    );
    let mx = usize::MAX;

    // ---- Section 13 parse wrappers and section 18/19 parse-error items, on every string.
    for s in &all {
        let bs = b(s);
        check!(c, "13 Pointer::parse", Pointer::parse(s).map(|p| p.as_str().as_bytes().to_vec()), a::pointer_parse_adapted(bs).map(|v| v.to_vec()), s);
        check!(c, "13 PointerBuf::try_from(&str)", PointerBuf::try_from(s.as_str()).map(|p| p.as_str().as_bytes().to_vec()), a::buf_try_from_str_adapted(bs), s);
        check!(c, "13 PointerBuf::from_str", PointerBuf::from_str(s).map(|p| p.as_str().as_bytes().to_vec()), a::buf_try_from_str_adapted(bs), s);
        check!(c, "13 PointerBuf::try_from(String)", PointerBuf::try_from(s.clone()).map(|p| p.as_str().as_bytes().to_vec()), a::buf_try_from_string_adapted(bs.to_vec()), s);
        let rel = PointerBuf::parse(s.clone()).map(|p| p.as_str().as_bytes().to_vec()).map_err(|r| {
            let (orig, subj) = r.decompose();
            (orig, subj.into_bytes())
        });
        let ad = a::buf_parse_adapted(bs.to_vec()).map_err(|r| (r.source, r.subject));
        check!(c, "13 PointerBuf::parse", rel, ad, s);
        let leaked: &'static str = Box::leak(s.clone().into_boxed_str());
        check!(c, "13 Pointer::from_static", caught(|| Pointer::from_static(leaked).as_str().as_bytes().to_vec()), caught(|| a::from_static_adapted(leaked.as_bytes()).to_vec()), s);
        if let Err(e) = Pointer::parse(s) {
            check!(c, "19 ParseError::invalid_encoding_len (own subject)", caught(|| e.invalid_encoding_len(s)), caught(|| a::invalid_encoding_len_adapted(&e, bs)), s);
            let rel = caught(|| e.labels(&s.to_string()).map(|it| it.collect::<Vec<Label>>()));
            let ad = caught(|| {
                let sp = a::parse_error_label_adapted(&e, bs);
                let text = match e {
                    ParseError::NoLeadingSlash => "must start with a slash ('/')",
                    ParseError::InvalidEncoding { .. } => "'~' must be followed by '0' or '1'",
                };
                Some(vec![Label::new(text.to_string(), sp.offset, sp.len)])
            });
            check!(c, "19 ParseError::labels (own subject)", rel, ad, s);
        }
        if let Err(e) = Token::from_encoded(s.as_str()) {
            let rel = caught(|| e.labels(&s.to_string()).map(|it| it.collect::<Vec<Label>>()));
            let ad = caught(|| {
                let sp = a::encoding_error_label_adapted(&e, bs);
                let text = match e.source {
                    jsonptr::InvalidEncoding::Tilde => {
                        if e.offset == s.len() { "incomplete escape sequence" } else { "must be 0 or 1" }
                    }
                    jsonptr::InvalidEncoding::Slash => "invalid character",
                };
                Some(vec![Label::new(text.to_string(), sp.offset, sp.len)])
            });
            check!(c, "19 EncodingError::labels (own subject)", rel, ad, s);
        }
        check!(c, "14 Token::is_next", Token::from_encoded(s.as_str()).map(|t| t.is_next()).ok(), Token::from_encoded(s.as_str()).ok().map(|_| a::is_next_adapted(bs)), s);
        check!(c, "21 str order/eq (any bytes)", (s.as_str().cmp("/a~0"), s.as_str() == "/a~0"), (a::str_cmp_adapted(bs, b("/a~0")), a::str_eq_adapted(bs, b("/a~0"))), s);
    }
    // Hand-built error values over short subjects (domain edges: N5, N7, N8, JSONPTR-003).
    let subjects = strings(2);
    for off in [0usize, 1, 2, 3, mx - 1, mx] {
        for soff in [0usize, 1, 2, mx] {
            for src in [jsonptr::InvalidEncoding::Tilde, jsonptr::InvalidEncoding::Slash] {
                let e = ParseError::InvalidEncoding { offset: off, source: EncodingError { offset: soff, source: src } };
                let ee = EncodingError { offset: off, source: src };
                for s in &subjects {
                    check!(c, "19 invalid_encoding_len (hand-built)", caught(|| e.invalid_encoding_len(s)), caught(|| a::invalid_encoding_len_adapted(&e, b(s))), (&e, s));
                    let rel = caught(|| e.labels(&s.to_string()).map(|it| it.collect::<Vec<Label>>()));
                    let ad = caught(|| {
                        let sp = a::parse_error_label_adapted(&e, b(s));
                        Some(vec![Label::new("'~' must be followed by '0' or '1'".to_string(), sp.offset, sp.len)])
                    });
                    check!(c, "19 ParseError::labels (hand-built)", rel, ad, (&e, s));
                    let rel = caught(|| ee.labels(&s.to_string()).map(|it| it.collect::<Vec<Label>>()));
                    let ad = caught(|| {
                        let sp = a::encoding_error_label_adapted(&ee, b(s));
                        let text = match ee.source {
                            jsonptr::InvalidEncoding::Tilde => {
                                if ee.offset == s.len() { "incomplete escape sequence" } else { "must be 0 or 1" }
                            }
                            jsonptr::InvalidEncoding::Slash => "invalid character",
                        };
                        Some(vec![Label::new(text.to_string(), sp.offset, sp.len)])
                    });
                    check!(c, "19 EncodingError::labels (hand-built)", rel, ad, (&ee, s));
                }
            }
        }
    }

    // ---- Sections 8-12, 21 on every valid pointer.
    for &s in &pointers {
        let p = Pointer::parse(s).unwrap();
        let bs = b(s);
        let n = p.count();
        check!(c, "8 count", n, a::count_adapted(bs), s);
        check!(c, "8 front", tok_bytes(p.front()), opt_vec(a::front_adapted(bs)), s);
        check!(c, "8 first", tok_bytes(p.first()), opt_vec(a::front_adapted(bs)), s);
        check!(c, "8 back", tok_bytes(p.back()), opt_vec(a::back_adapted(bs)), s);
        check!(c, "8 last", tok_bytes(p.last()), opt_vec(a::back_adapted(bs)), s);
        check!(c, "8 split_back", p.split_back().map(|(h, t)| (h.as_str().as_bytes().to_vec(), t.encoded().as_bytes().to_vec())), a::split_back_adapted(bs).map(|(h, t)| (h.to_vec(), t.to_vec())), s);
        check!(c, "8 parent", ptr_bytes(p.parent()), opt_vec(a::parent_adapted(bs)), s);
        for i in (0..=n + 2).chain([mx - 1, mx]) {
            check!(c, "8 get(usize)", tok_bytes(p.get(i)), opt_vec(a::get_index_adapted(bs, i)), (s, i));
        }
        // full Tokens sequence, and that it stays exhausted
        let rel: Vec<Vec<u8>> = p.tokens().map(|t| t.encoded().as_bytes().to_vec()).collect();
        let mut it = a::tokens_adapted(bs);
        let mut ad = Vec::new();
        while let Some(t) = a::tokens_next_adapted(&mut it) {
            ad.push(t.to_vec());
        }
        let extra = (a::tokens_next_adapted(&mut it).is_none(), a::tokens_next_adapted(&mut it).is_none());
        check!(c, "8 Tokens::next sequence", (rel.clone(), true, true), (ad, extra.0, extra.1), s);
        let rel_into: Vec<Vec<u8>> = (&p.to_buf()).into_iter().map(|t| t.encoded().as_bytes().to_vec()).collect();
        check!(c, "8 IntoIterator for &PointerBuf", rel_into, rel.clone(), s);
        let relc: Vec<Option<Vec<u8>>> = p.components().map(|c| match c { Component::Root => None, Component::Token(t) => Some(t.encoded().as_bytes().to_vec()) }).collect();
        let mut cit = a::components_adapted(bs);
        let mut adc = Vec::new();
        while let Some(x) = a::components_next_adapted(&mut cit) {
            adc.push(match x { ComponentAdapted::Root => None, ComponentAdapted::Token(t) => Some(t.to_vec()) });
        }
        check!(c, "8 Components::next sequence", relc, adc, s);
        for t in p.tokens() {
            let rel = match Component::from(t.clone()) { Component::Token(t) => Some(t.encoded().as_bytes().to_vec()), Component::Root => None };
            let ad = match a::component_from_token_adapted(t.encoded().as_bytes()) { ComponentAdapted::Token(t) => Some(t.to_vec()), ComponentAdapted::Root => None };
            check!(c, "8 Component::from(Token)", rel, ad, s);
        }
        // Section 9 ranges
        let vals: Vec<usize> = (0..=n + 2).chain([mx - 1, mx]).collect();
        for &x in &vals {
            check!(c, "9 get(s..)", ptr_bytes(p.get(x..)), opt_vec(a::get_range_from_adapted(bs, x)), (s, x));
            check!(c, "9 get(..e)", ptr_bytes(p.get(..x)), opt_vec(a::get_range_to_adapted(bs, x)), (s, x));
            check!(c, "9 get(..=e)", ptr_bytes(p.get(..=x)), opt_vec(a::get_range_to_inclusive_adapted(bs, x)), (s, x));
            for &y in &vals {
                check!(c, "9 get(s..e)", ptr_bytes(p.get(x..y)), opt_vec(a::get_range_adapted(bs, x, y)), (s, x, y));
                check!(c, "9 get(s..=e)", ptr_bytes(p.get(x..=y)), opt_vec(a::get_range_inclusive_adapted(bs, x, y)), (s, x, y));
            }
        }
        check!(c, "9 get(..)", ptr_bytes(p.get(..)), opt_vec(a::get_range_full_adapted(bs)), s);
        let bounds = |v: usize| [(Bound::Included(v), BoundAdapted::Included(v)), (Bound::Excluded(v), BoundAdapted::Excluded(v))];
        let mut bl: Vec<(Bound<usize>, BoundAdapted)> = vec![(Bound::Unbounded, BoundAdapted::Unbounded)];
        for &x in &vals {
            bl.extend(bounds(x));
        }
        for (rs, as_) in &bl {
            for (re, ae) in &bl {
                let rel = caught(|| ptr_bytes(p.get((*rs, *re))));
                let ad = caught(|| opt_vec(a::get_bounds_adapted(bs, *as_, *ae)));
                check!(c, "9 get((Bound, Bound))", rel, ad, (s, rs, re));
            }
        }
        // Section 10
        for off in (0..=s.len() + 1).chain([mx]) {
            #[allow(deprecated)]
            let dep = p.split_at(off).map(|(h, t)| (h.as_str().as_bytes().to_vec(), t.as_str().as_bytes().to_vec()));
            let rel = p.split_at_offset(off).map(|(h, t)| (h.as_str().as_bytes().to_vec(), t.as_str().as_bytes().to_vec()));
            let ad = a::split_at_offset_adapted(bs, off).map(|(h, t)| (h.to_vec(), t.to_vec()));
            check!(c, "10 split_at_offset", rel.clone(), ad, (s, off));
            check!(c, "10 split_at (deprecated)", dep, rel, (s, off));
        }
        // Section 12 single-buffer mutations
        let buf = p.to_buf();
        check!(c, "12 to_buf / ToOwned", (buf.as_str().as_bytes().to_vec(), p.to_owned().as_str().as_bytes().to_vec()), (a::to_buf_adapted(bs), a::to_buf_adapted(bs)), s);
        {
            let mut r = buf.clone();
            let rv = r.pop_back().map(|t| t.encoded().as_bytes().to_vec());
            let mut v = bs.to_vec();
            let av = a::pop_back_adapted(&mut v);
            check!(c, "12 pop_back", (rv, r.as_str().as_bytes().to_vec()), (av, v), s);
        }
        {
            let mut r = buf.clone();
            let rv = r.pop_front().map(|t| t.encoded().as_bytes().to_vec());
            let mut v = bs.to_vec();
            let av = a::pop_front_adapted(&mut v);
            check!(c, "12 pop_front", (rv, r.as_str().as_bytes().to_vec()), (av, v), s);
        }
        {
            let mut r = buf.clone();
            r.clear();
            let mut v = bs.to_vec();
            a::clear_adapted(&mut v);
            check!(c, "12 clear", r.as_str().as_bytes().to_vec(), v, s);
        }
        check!(c, "21 PointerBuf::clone", buf.clone().as_str().as_bytes().to_vec(), a::buf_clone_adapted(&bs.to_vec()), s);
        check!(c, "21 is_root/is_empty/len", (p.is_root(), p.is_empty(), p.len()), (a::is_root_adapted(bs), a::is_root_adapted(bs), a::len_adapted(bs)), s);
        for t in &tokens {
            let tb = b(t);
            let tk = Token::from_encoded(t.as_str()).unwrap();
            let mut r = buf.clone();
            r.push_back(tk.clone());
            let mut v = bs.to_vec();
            a::push_back_adapted(&mut v, tb);
            check!(c, "12 push_back", r.as_str().as_bytes().to_vec(), v.clone(), (s, t));
            check!(c, "12 with_trailing_token", p.with_trailing_token(tk.clone()).as_str().as_bytes().to_vec(), a::with_trailing_token_adapted(bs, tb), (s, t));
            let mut r = buf.clone();
            r.push_front(tk.clone());
            let mut v = bs.to_vec();
            a::push_front_adapted(&mut v, tb);
            check!(c, "12 push_front", r.as_str().as_bytes().to_vec(), v, (s, t));
            check!(c, "12 with_leading_token", p.with_leading_token(tk.clone()).as_str().as_bytes().to_vec(), a::with_leading_token_adapted(bs, tb), (s, t));
            for i in (0..=n + 1).chain([mx]) {
                let mut r = buf.clone();
                let rv = r.replace(i, tk.clone()).map(|o| o.map(|t| t.encoded().as_bytes().to_vec()));
                let mut v = bs.to_vec();
                let av = a::replace_adapted(&mut v, i, tb);
                check!(c, "12 replace", (rv, r.as_str().as_bytes().to_vec()), (av, v), (s, i, t));
            }
        }
    }
    // from_tokens on token lists of length <= 3
    let mut lists: Vec<Vec<String>> = vec![vec![]];
    for _ in 0..3 {
        let mut next = Vec::new();
        for l in &lists {
            if l.len() == lists.last().unwrap().len() {
                for t in &tokens {
                    let mut m = l.clone();
                    m.push(t.clone());
                    next.push(m);
                }
            }
        }
        lists.extend(next);
    }
    for l in &lists {
        let rel = PointerBuf::from_tokens(l.iter().map(|t| Token::from_encoded(t.as_str()).unwrap()));
        let ad = a::from_tokens_adapted(&l.iter().map(|t| t.as_bytes().to_vec()).collect::<Vec<_>>());
        check!(c, "12 from_tokens", rel.as_str().as_bytes().to_vec(), ad, l);
        if l.len() == 1 {
            let one = PointerBuf::from(Token::from_encoded(l[0].as_str()).unwrap());
            check!(c, "12 From<Token>", one.as_str().as_bytes().to_vec(), a::from_tokens_adapted(&[l[0].as_bytes().to_vec()]), l);
        }
    }
    check!(c, "12 new/root/default", (PointerBuf::new().as_str().len(), PointerBuf::root().as_str().len(), PointerBuf::default().as_str().len()), (a::buf_new_adapted().len(), 0, 0), "");
    // Tokens: section 14
    for t in &tokens {
        let tk = Token::from_encoded(t.as_str()).unwrap();
        check!(c, "14 Token::encoded/into_encoded", (tk.encoded().as_bytes().to_vec(), tk.clone().into_encoded().as_bytes().to_vec()), (a::token_encoded_adapted(b(t)).to_vec(), a::token_encoded_adapted(b(t)).to_vec()), t);
        check!(c, "14 Token::to_owned/into_owned/clone/from(&Token)", (tk.to_owned().encoded().as_bytes().to_vec(), tk.clone().into_owned().encoded().as_bytes().to_vec(), Token::from(&tk).encoded().as_bytes().to_vec()), (a::token_to_owned_adapted(b(t)), a::token_to_owned_adapted(b(t)), a::token_to_owned_adapted(b(t))), t);
    }
    for s in strings(3) {
        let sot = jsonptr::index::StringOrToken::from(s.clone());
        check!(c, "14 StringOrToken from(String)/deref", (&*sot).as_bytes().to_vec(), a::sot_deref_adapted(&a::sot_from_string_adapted(s.as_bytes().to_vec())).to_vec(), &s);
        let tok = Token::new(s.clone());
        let enc = tok.encoded().as_bytes().to_vec();
        let sot = jsonptr::index::StringOrToken::from(tok);
        check!(c, "14 StringOrToken from(Token)/deref", (&*sot).as_bytes().to_vec(), a::sot_deref_adapted(&a::sot_from_token_adapted(enc)).to_vec(), &s);
    }
    // ---- Pairs: sections 11, 12 (append/concat), 21 (eq/order).
    for &x in &small {
        let px = Pointer::parse(x).unwrap();
        for &y in &small {
            let py = Pointer::parse(y).unwrap();
            let (bx, by) = (b(x), b(y));
            check!(c, "11 starts_with", px.starts_with(py), a::starts_with_adapted(bx, by), (x, y));
            check!(c, "11 ends_with", px.ends_with(py), a::ends_with_adapted(bx, by), (x, y));
            check!(c, "11 strip_prefix", ptr_bytes(px.strip_prefix(py)), opt_vec(a::strip_prefix_adapted(bx, by)), (x, y));
            check!(c, "11 strip_suffix", ptr_bytes(px.strip_suffix(py)), opt_vec(a::strip_suffix_adapted(bx, by)), (x, y));
            check!(c, "11 intersection", px.intersection(py).as_str().as_bytes().to_vec(), a::intersection_adapted(bx, by).to_vec(), (x, y));
            let mut r = px.to_buf();
            r.append(py);
            let mut v = bx.to_vec();
            a::append_adapted(&mut v, by);
            check!(c, "12 append", r.as_str().as_bytes().to_vec(), v, (x, y));
            check!(c, "12 concat", px.concat(py).as_str().as_bytes().to_vec(), a::concat_adapted(bx, by), (x, y));
            let bx_ = px.to_buf();
            let by_ = py.to_buf();
            let rel_eq = [px == py, *px == *y, *px == y, px == y.to_string(), px == by_, bx_ == *py, bx_ == by_, *x == *py, x.to_string() == *py, bx_ == y, bx_ == y.to_string(), x == by_, *x == by_];
            let ad = a::str_eq_adapted(bx, by);
            check!(c, "21 PartialEq (13 directions)", rel_eq, [ad; 13], (x, y));
            let rel_ord = [px.partial_cmp(py), px.partial_cmp(&by_), bx_.partial_cmp(py), bx_.partial_cmp(&by_), x.partial_cmp(py), x.to_string().partial_cmp(py), bx_.partial_cmp(&y), (&px).partial_cmp(&y), Some(px.cmp(py)), Some(bx_.cmp(&by_))];
            let ad = Some(a::str_cmp_adapted(bx, by));
            check!(c, "21 PartialOrd/Ord (10 directions)", rel_ord, [ad; 10], (x, y));
            for (tx, ty) in px.tokens().zip(py.tokens()) {
                check!(c, "21 Token eq/cmp", (tx == ty, tx.cmp(&ty)), (a::str_eq_adapted(tx.encoded().as_bytes(), ty.encoded().as_bytes()), a::str_cmp_adapted(tx.encoded().as_bytes(), ty.encoded().as_bytes())), (x, y));
            }
            let cx: Vec<Component> = px.components().collect();
            let cy: Vec<Component> = py.components().collect();
            let cxa: Vec<ComponentAdapted> = { let mut it = a::components_adapted(bx); let mut v = vec![]; while let Some(c) = a::components_next_adapted(&mut it) { v.push(c); } v };
            let cya: Vec<ComponentAdapted> = { let mut it = a::components_adapted(by); let mut v = vec![]; while let Some(c) = a::components_next_adapted(&mut it) { v.push(c); } v };
            for i in 0..cx.len().min(cy.len()) {
                check!(c, "21 Component eq/cmp", (cx[i] == cy[i], cx[i].cmp(&cy[i])), (a::component_eq_adapted(cxa[i], cya[i]), a::component_cmp_adapted(cxa[i], cya[i])), (x, y, i));
            }
        }
    }
    tier4::run(&mut c.0);
    tier4::run5(&mut c.0);
    let _ = (Index::Next, Ordering::Equal, ReplaceError { index: 0, count: 0 });
    let total: u64 = c.0.values().sum();
    for (k, v) in &c.0 {
        println!("{k}: {v}");
    }
    println!("total comparisons: {total}");
    println!("all compared results agree");
}
