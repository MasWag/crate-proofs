//! Differential comparison of jsonptr 0.8.2 release APIs with the adapted
//! byte-slice bodies of the Aeneas `adapted` profile.
//!
//! Inputs: every string of at most `MAX_LEN` characters over `ALPHABET`, plus
//! decimal strings around `usize::MAX`. Complete results are compared,
//! including every error field. Agreement on these inputs is evidence for the
//! release-correspondence obligations, not a proof of equivalence.

use jsonptr::adapted::{
    decoded_adapted, from_encoded_adapted, from_str_adapted, new_adapted, resolve_adapted,
    resolve_recursive_adapted,
    resolve_step_adapted, split_front_adapted, validate_adapted, DocAdapted, IntErrorKindAdapted,
    ParseIndexErrorAdapted, ResolveErrorAdapted,
};
use jsonptr::index::{Index, ParseIndexError};
use jsonptr::resolve::{Error as ResolveError, Resolve};
use jsonptr::{Pointer, Token};

use serde_json::{Map, Value};
use std::borrow::Cow;
use std::num::IntErrorKind;
use std::str::FromStr;

const ALPHABET: [char; 11] = ['/', '~', '0', '1', '2', '9', '-', '+', 'a', '\0', 'é'];
const MAX_LEN: usize = 7;

#[derive(Default)]
struct Counts {
    strings: u64,
    t1_validate: u64,
    t2_encode: u64,
    t3_decode: u64,
    t4_from_encoded: u64,
    t5_index: u64,
    t6_split: u64,
    t7_resolve: u64,
    outcomes: std::collections::BTreeMap<String, u64>,
}

impl Counts {
    fn tally(&mut self, key: String) {
        *self.outcomes.entry(key).or_default() += 1;
    }
}

fn strings(max_len: usize, mut f: impl FnMut(&str)) {
    let mut idx: Vec<usize> = Vec::new();
    let mut buf = String::new();
    loop {
        buf.clear();
        buf.extend(idx.iter().map(|&i| ALPHABET[i]));
        f(&buf);
        // next string in length-lexicographic order
        let mut pos = idx.len();
        loop {
            if pos == 0 {
                if idx.len() == max_len {
                    return;
                }
                idx = vec![0; idx.len() + 1];
                break;
            }
            pos -= 1;
            if idx[pos] + 1 < ALPHABET.len() {
                idx[pos] += 1;
                for j in pos + 1..idx.len() {
                    idx[j] = 0;
                }
                break;
            }
        }
    }
}

/// Neutral observation of an index error: variant, character offset, or the
/// `IntErrorKind` of the wrapped `ParseIntError`.
#[derive(Debug, PartialEq, Eq)]
enum IdxErr {
    LeadingZeros,
    InvalidCharacter(usize),
    Empty,
    PosOverflow,
}

fn index_error(e: &ParseIndexError) -> IdxErr {
    match e {
        ParseIndexError::LeadingZeros => IdxErr::LeadingZeros,
        ParseIndexError::InvalidCharacter(c) => IdxErr::InvalidCharacter(c.offset()),
        ParseIndexError::InvalidInteger(p) => match p.kind() {
            IntErrorKind::Empty => IdxErr::Empty,
            IntErrorKind::PosOverflow => IdxErr::PosOverflow,
            other => panic!("unexpected IntErrorKind {other:?}"),
        },
    }
}

fn index_error_adapted(e: &ParseIndexErrorAdapted) -> IdxErr {
    match e {
        ParseIndexErrorAdapted::LeadingZeros => IdxErr::LeadingZeros,
        ParseIndexErrorAdapted::InvalidCharacter(c) => IdxErr::InvalidCharacter(c.offset()),
        ParseIndexErrorAdapted::InvalidInteger(IntErrorKindAdapted::Empty) => IdxErr::Empty,
        ParseIndexErrorAdapted::InvalidInteger(IntErrorKindAdapted::PosOverflow) => IdxErr::PosOverflow,
    }
}

fn check_index(s: &str, counts: &mut Counts) {
    let release = Index::from_str(s).map_err(|e| index_error(&e));
    let adapted = from_str_adapted(s.as_bytes()).map_err(|e| index_error_adapted(&e));
    assert_eq!(release, adapted, "from_str({s:?})");
    counts.t5_index += 1;
    counts.tally(match &release {
        Ok(Index::Next) => "index:Next".into(),
        Ok(Index::Num(_)) => "index:Num".into(),
        Err(e) => format!("index:{}", format!("{e:?}").split('(').next().unwrap()),
    });
}

fn check_token(s: &str, counts: &mut Counts) {
    // Target 4
    let release = Token::from_encoded(s);
    let adapted = from_encoded_adapted(s.as_bytes());
    match (&release, &adapted) {
        (Ok(t), Ok(b)) => {
            assert_eq!(t.encoded().as_bytes(), *b, "from_encoded({s:?})");
            assert!(std::ptr::eq(*b, s.as_bytes()), "from_encoded reuse {s:?}");
        }
        (Err(e), Err(f)) => assert_eq!(e, f, "from_encoded({s:?})"),
        _ => panic!("from_encoded({s:?}): {release:?} vs {adapted:?}"),
    }
    counts.t4_from_encoded += 1;
    counts.tally(match &release {
        Ok(_) => "from_encoded:Ok".into(),
        Err(e) => format!("from_encoded:{:?}", e.source),
    });

    // Target 2
    let tok = Token::new(s);
    let enc = tok.encoded().as_bytes().to_vec();
    let borrowed = matches!(tok.clone().into_encoded(), Cow::Borrowed(_));
    match new_adapted(s.as_bytes()) {
        None => {
            assert!(borrowed, "new({s:?}) reuse");
            assert_eq!(enc, s.as_bytes(), "new({s:?})");
        }
        Some(v) => {
            assert!(!borrowed, "new({s:?}) owned");
            assert_eq!(enc, v, "new({s:?})");
        }
    }
    counts.t2_encode += 1;

    // Target 3 on lawful tokens: the encoding of s, and s itself when lawful.
    let mut lawful = vec![tok];
    if let Ok(t) = release {
        lawful.push(t);
    }
    for t in &lawful {
        let rel = t.decoded();
        let stored_borrowed = matches!(t.clone().into_encoded(), Cow::Borrowed(_));
        match decoded_adapted(t.encoded().as_bytes()) {
            None => {
                assert_eq!(rel.as_bytes(), t.encoded().as_bytes(), "decoded({t:?})");
                assert_eq!(matches!(rel, Cow::Borrowed(_)), stored_borrowed, "decoded({t:?}) reuse");
            }
            Some(v) => {
                assert!(matches!(rel, Cow::Owned(_)), "decoded({t:?}) owned");
                assert_eq!(rel.as_bytes(), v.as_slice(), "decoded({t:?})");
            }
        }
        counts.t3_decode += 1;
    }
    // Token::to_index applies from_str to the encoded token.
    let t = Token::new(s);
    assert_eq!(
        t.to_index().map_err(|e| index_error(&e)),
        from_str_adapted(t.encoded().as_bytes()).map_err(|e| index_error_adapted(&e)),
        "to_index({s:?})"
    );
}

fn check_pointer(s: &str, docs: &[(DocAdapted, Value)], counts: &mut Counts) {
    let release = Pointer::parse(s);
    let adapted = validate_adapted(s.as_bytes());
    match (&release, &adapted) {
        (Ok(p), Ok(b)) => {
            assert_eq!(p.as_str().as_bytes(), *b, "parse({s:?})");
            assert!(std::ptr::eq(*b, s.as_bytes()), "validate reuse {s:?}");
        }
        (Err(e), Err(f)) => assert_eq!(e, f, "parse({s:?})"),
        _ => panic!("parse({s:?}): {release:?} vs {adapted:?}"),
    }
    counts.t1_validate += 1;
    counts.tally(match &release {
        Ok(_) => "validate:Ok".into(),
        Err(e) => format!("validate:{}", format!("{e:?}").split(' ').next().unwrap()),
    });
    let Ok(ptr) = release else { return };

    // Target 6: split_front and the whole token sequence.
    let mut rel = ptr;
    let mut ada: &[u8] = s.as_bytes();
    loop {
        match (rel.split_front(), split_front_adapted(ada)) {
            (None, None) => break,
            (Some((t, r)), Some((ta, ra))) => {
                assert_eq!(t.encoded().as_bytes(), ta, "split_front({s:?})");
                assert_eq!(r.as_str().as_bytes(), ra, "split_front rest({s:?})");
                rel = r;
                ada = ra;
            }
            (x, y) => panic!("split_front({s:?}): {x:?} vs {y:?}"),
        }
    }
    let toks: Vec<String> = ptr.tokens().map(|t| t.encoded().to_string()).collect();
    let mut ada_toks = Vec::new();
    let mut rest: &[u8] = s.as_bytes();
    while let Some((t, r)) = split_front_adapted(rest) {
        ada_toks.push(String::from_utf8(t.to_vec()).unwrap());
        rest = r;
    }
    assert_eq!(toks, ada_toks, "tokens({s:?})");
    counts.t6_split += 1;

    // Target 7: release resolution on serde_json vs the adapted loop and the
    // step function and the recursive form over the corresponding local document.
    for (doc, json) in docs {
        let release = json.resolve(ptr);
        let adapted = resolve_adapted(doc, s.as_bytes());
        let stepped = resolve_by_steps(doc, s.as_bytes());
        assert_eq!(adapted, stepped, "loop vs steps {s:?}");
        assert_eq!(adapted, resolve_recursive_adapted(doc, s.as_bytes()), "loop vs recursion {s:?}");
        match (&release, &adapted) {
            (Ok(v), Ok(d)) => assert_eq!(*v, &to_json(d), "resolve({s:?})"),
            (Err(e), Err(f)) => assert_eq!(map_resolve_error(e), map_resolve_error_adapted(f), "resolve({s:?})"),
            _ => panic!("resolve({s:?}): {release:?} vs {adapted:?}"),
        }
        counts.t7_resolve += 1;
        counts.tally(match &release {
            Ok(_) => "resolve:Ok".into(),
            Err(e) => format!("resolve:{}", format!("{:?}", map_resolve_error(e)).split('(').next().unwrap()),
        });
    }
}

fn resolve_by_steps<'d>(doc: &'d DocAdapted, ptr: &[u8]) -> Result<&'d DocAdapted, ResolveErrorAdapted> {
    let (mut value, mut rest, mut position, mut offset) = (doc, ptr, 0usize, 0usize);
    while let Some((tok, r)) = split_front_adapted(rest) {
        value = resolve_step_adapted(value, tok, position, offset)?;
        offset += 1 + tok.len();
        position += 1;
        rest = r;
    }
    Ok(value)
}

/// Neutral observation of a resolution error with every field.
#[derive(Debug, PartialEq, Eq)]
enum ResErr {
    FailedToParseIndex(usize, usize, IdxErr),
    OutOfBounds(usize, usize, usize, usize),
    NotFound(usize, usize),
    Unreachable(usize, usize),
}

fn map_resolve_error(e: &ResolveError) -> ResErr {
    match e {
        ResolveError::FailedToParseIndex { position, offset, source } => {
            ResErr::FailedToParseIndex(*position, *offset, index_error(source))
        }
        ResolveError::OutOfBounds { position, offset, source } => {
            ResErr::OutOfBounds(*position, *offset, source.length, source.index)
        }
        ResolveError::NotFound { position, offset } => ResErr::NotFound(*position, *offset),
        ResolveError::Unreachable { position, offset } => ResErr::Unreachable(*position, *offset),
    }
}

fn map_resolve_error_adapted(e: &ResolveErrorAdapted) -> ResErr {
    match e {
        ResolveErrorAdapted::FailedToParseIndex { position, offset, source } => {
            ResErr::FailedToParseIndex(*position, *offset, index_error_adapted(source))
        }
        ResolveErrorAdapted::OutOfBounds { position, offset, source } => {
            ResErr::OutOfBounds(*position, *offset, source.length, source.index)
        }
        ResolveErrorAdapted::NotFound { position, offset } => ResErr::NotFound(*position, *offset),
        ResolveErrorAdapted::Unreachable { position, offset } => ResErr::Unreachable(*position, *offset),
    }
}

fn to_json(d: &DocAdapted) -> Value {
    match d {
        DocAdapted::Leaf(n) => Value::from(*n),
        DocAdapted::Array(items) => Value::Array(items.iter().map(to_json).collect()),
        DocAdapted::Object(members) => {
            let mut m = Map::new();
            for (k, v) in members {
                m.insert(String::from_utf8(k.clone()).unwrap(), to_json(v));
            }
            Value::Object(m)
        }
    }
}

fn obj(members: Vec<(&str, DocAdapted)>) -> DocAdapted {
    DocAdapted::Object(members.into_iter().map(|(k, v)| (k.as_bytes().to_vec(), v)).collect())
}

fn documents() -> Vec<(DocAdapted, Value)> {
    use DocAdapted::{Array, Leaf};
    let docs = vec![
        Leaf(0),
        Array(vec![]),
        Array(vec![Leaf(1), Array(vec![Leaf(2), Leaf(3)]), obj(vec![("a", Leaf(4))])]),
        obj(vec![
            ("a", Array(vec![Leaf(5), obj(vec![("", Leaf(6)), ("~", Leaf(7)), ("/", Array(vec![Leaf(8)]))])])),
            ("", obj(vec![("", Array(vec![Leaf(9), Leaf(10), Leaf(11)]))])),
            ("0", Leaf(12)),
            ("1", Array(vec![obj(vec![("é", Leaf(13)), ("\0", Leaf(14))])])),
            ("~1", Leaf(15)),
            ("-", Array(vec![Leaf(16)])),
            ("é", obj(vec![("9", Leaf(17)), ("+", Leaf(18))])),
        ]),
    ];
    docs.into_iter()
        .map(|d| {
            let j = to_json(&d);
            (d, j)
        })
        .collect()
}

fn main() {
    let docs = documents();
    let mut counts = Counts::default();
    strings(MAX_LEN, |s| {
        counts.strings += 1;
        check_index(s, &mut counts);
        check_token(s, &mut counts);
        check_pointer(s, &docs, &mut counts);
    });
    // Decimal strings around usize::MAX and powers of ten, with and without a
    // leading zero, sign or trailing non-digit.
    let mut boundary: Vec<String> = Vec::new();
    let max = usize::MAX as u128;
    for k in 0..=2000u128 {
        boundary.push((max - k).to_string());
        boundary.push((max + 1 + k).to_string());
    }
    for e in 15..=22u32 {
        let p = 10u128.pow(e);
        for d in [p - 1, p, p + 1] {
            boundary.push(d.to_string());
        }
    }
    boundary.push("9".repeat(40));
    boundary.push(format!("{}0", usize::MAX));
    let extra: Vec<String> = boundary
        .iter()
        .flat_map(|b| [b.clone(), format!("0{b}"), format!("+{b}"), format!("{b}a"), format!("{b}é")])
        .collect();
    let mut boundary_count = 0u64;
    for s in &extra {
        check_index(s, &mut counts);
        check_token(s, &mut counts);
        boundary_count += 1;
        let p = format!("/{s}");
        check_pointer(&p, &docs, &mut counts);
        let big = DocAdapted::Array(vec![DocAdapted::Leaf(0)]);
        let big_json = to_json(&big);
        let r = big_json.resolve(Pointer::parse(&p).unwrap());
        let a = resolve_adapted(&big, p.as_bytes());
        assert_eq!(a, resolve_recursive_adapted(&big, p.as_bytes()), "loop vs recursion {p:?}");
        match (&r, &a) {
            (Ok(v), Ok(d)) => assert_eq!(*v, &to_json(d)),
            (Err(e), Err(f)) => assert_eq!(map_resolve_error(e), map_resolve_error_adapted(f), "resolve({p:?})"),
            _ => panic!("resolve({p:?}): {r:?} vs {a:?}"),
        }
    }
    let profile = if cfg!(debug_assertions) { "debug" } else { "release" };
    println!(
        "differential[{profile}] alphabet={} max_len={MAX_LEN} strings={} boundary_strings={boundary_count} documents={}",
        ALPHABET.len(),
        counts.strings,
        docs.len()
    );
    println!(
        "  comparisons: validate={} encode={} decode={} from_encoded={} index={} split/tokens={} resolve={}",
        counts.t1_validate,
        counts.t2_encode,
        counts.t3_decode,
        counts.t4_from_encoded,
        counts.t5_index,
        counts.t6_split,
        counts.t7_resolve
    );
    for (k, v) in &counts.outcomes {
        println!("  outcome {k}: {v}");
    }
    println!("  all compared results agree (finite evidence, not a proof)");
}
