//! Tier 4 differential: release `serde_json::Value` methods vs the adapted
//! bodies over `DocAdapted`. Documents are compared after sorting object
//! members by key (serde_json's map order is outside the contract).

use jsonptr::adapted::{DocAdapted, IntErrorKindAdapted, ParseIndexErrorAdapted, ResolveErrorAdapted};
use jsonptr::adapted_api as a;
use jsonptr::adapted_api::AssignErrorAdapted;
use jsonptr::index::ParseIndexError;
use jsonptr::{Assign, Delete, Pointer, ResolveMut};
use serde_json::{Map, Value};
use std::num::IntErrorKind;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn to_doc(v: &Value) -> DocAdapted {
    match v {
        Value::Null => DocAdapted::Leaf(0),
        Value::Number(n) => DocAdapted::Leaf(n.as_u64().unwrap() + 1),
        Value::Array(xs) => DocAdapted::Array(xs.iter().map(to_doc).collect()),
        Value::Object(m) => DocAdapted::Object(m.iter().map(|(k, v)| (k.as_bytes().to_vec(), to_doc(v))).collect()),
        _ => unreachable!(),
    }
}

fn norm(d: &DocAdapted) -> DocAdapted {
    match d {
        DocAdapted::Leaf(x) => DocAdapted::Leaf(*x),
        DocAdapted::Array(xs) => DocAdapted::Array(xs.iter().map(norm).collect()),
        DocAdapted::Object(ms) => {
            let mut v: Vec<(Vec<u8>, DocAdapted)> = ms.iter().map(|(k, d)| (k.clone(), norm(d))).collect();
            v.sort_by(|x, y| x.0.cmp(&y.0));
            DocAdapted::Object(v)
        }
    }
}

fn pie(e: &ParseIndexError) -> ParseIndexErrorAdapted {
    match e {
        ParseIndexError::LeadingZeros => ParseIndexErrorAdapted::LeadingZeros,
        ParseIndexError::InvalidCharacter(c) => ParseIndexErrorAdapted::InvalidCharacter(c.clone()),
        ParseIndexError::InvalidInteger(p) => ParseIndexErrorAdapted::InvalidInteger(match p.kind() {
            IntErrorKind::Empty => IntErrorKindAdapted::Empty,
            IntErrorKind::PosOverflow => IntErrorKindAdapted::PosOverflow,
            k => panic!("unexpected kind {k:?}"),
        }),
    }
}

fn rerr(e: &jsonptr::resolve::Error) -> ResolveErrorAdapted {
    use jsonptr::resolve::Error as E;
    match e {
        E::FailedToParseIndex { position, offset, source } => ResolveErrorAdapted::FailedToParseIndex { position: *position, offset: *offset, source: pie(source) },
        E::OutOfBounds { position, offset, source } => ResolveErrorAdapted::OutOfBounds { position: *position, offset: *offset, source: source.clone() },
        E::NotFound { position, offset } => ResolveErrorAdapted::NotFound { position: *position, offset: *offset },
        E::Unreachable { position, offset } => ResolveErrorAdapted::Unreachable { position: *position, offset: *offset },
    }
}

fn aerr(e: &jsonptr::assign::Error) -> AssignErrorAdapted {
    use jsonptr::assign::Error as E;
    match e {
        E::FailedToParseIndex { position, offset, source } => AssignErrorAdapted::FailedToParseIndex { position: *position, offset: *offset, source: pie(source) },
        E::OutOfBounds { position, offset, source } => AssignErrorAdapted::OutOfBounds { position: *position, offset: *offset, source: source.clone() },
    }
}

fn docs() -> Vec<Value> {
    let leaves = vec![Value::Null, Value::from(1u64)];
    let keys = ["a", "0", "~", "/", ""];
    let mut lvl: Vec<Value> = leaves.clone();
    for _ in 0..2 {
        let mut next = leaves.clone();
        for x in &lvl {
            next.push(Value::Array(vec![x.clone()]));
            next.push(Value::Array(vec![Value::Null, x.clone()]));
            for k in keys {
                let mut m = Map::new();
                m.insert(k.to_string(), x.clone());
                next.push(Value::Object(m.clone()));
                m.insert("b".to_string(), Value::Null);
                next.push(Value::Object(m));
            }
        }
        next.push(Value::Array(vec![]));
        next.push(Value::Object(Map::new()));
        lvl = next;
    }
    lvl
}

fn pointers() -> Vec<String> {
    let toks = ["a", "b", "0", "1", "-", "~0", "~1", "", "00", "x"];
    let mut out = vec![String::new()];
    let mut layer = vec![String::new()];
    for _ in 0..3 {
        let mut next = vec![];
        for p in &layer {
            for t in toks {
                next.push(format!("{p}/{t}"));
            }
        }
        out.extend(next.iter().cloned());
        layer = next;
    }
    out
}

pub fn run(counts: &mut std::collections::BTreeMap<&'static str, u64>) {
    let ds = docs();
    let ps = pointers();
    println!("tier 4 inputs: {} documents, {} pointers", ds.len(), ps.len());
    for d in &ds {
        for p in &ps {
            let ptr = Pointer::parse(p).unwrap();
            let pb = p.as_bytes();
            // resolve_mut + write-back
            {
                let mut rv = d.clone();
                let rel = catch_unwind(AssertUnwindSafe(|| match rv.resolve_mut(ptr) {
                    Ok(node) => { let old = to_doc(node); *node = Value::from(97u64); Ok(old) }
                    Err(e) => Err(rerr(&e)),
                }));
                let mut ad = to_doc(d);
                let adr = catch_unwind(AssertUnwindSafe(|| match a::resolve_mut_adapted(&mut ad, pb) {
                    Ok(node) => { let old = node.clone(); *node = DocAdapted::Leaf(98); Ok(old) }
                    Err(e) => Err(e),
                }));
                let rel = rel.map(|r| r.map(|o| norm(&o))).map_err(|_| ());
                let adr = adr.map(|r| r.map(|o| norm(&o))).map_err(|_| ());
                assert!(rel == adr, "MISMATCH resolve_mut {d} {p}: {rel:?} vs {adr:?}");
                assert!(norm(&to_doc(&rv)) == norm(&ad), "MISMATCH resolve_mut doc {d} {p}");
                *counts.entry("15 resolve_mut + write-back").or_default() += 1;
            }
            // assign
            {
                let mut rv = d.clone();
                let rel = catch_unwind(AssertUnwindSafe(|| rv.assign(ptr, Value::from(6u64)).map(|o| o.map(|x| norm(&to_doc(&x)))).map_err(|e| aerr(&e)))).map_err(|_| ());
                let mut ad = to_doc(d);
                let adr = catch_unwind(AssertUnwindSafe(|| a::assign_adapted(&mut ad, pb, DocAdapted::Leaf(7)).map(|o| o.map(|x| norm(&x))))).map_err(|_| ());
                assert!(rel == adr, "MISMATCH assign {d} {p}: {rel:?} vs {adr:?}");
                assert!(norm(&to_doc(&rv)) == norm(&ad), "MISMATCH assign doc {d} {p}");
                *counts.entry("16 assign").or_default() += 1;
            }
            // delete (JSON)
            {
                let mut rv = d.clone();
                let rel = catch_unwind(AssertUnwindSafe(|| rv.delete(ptr).map(|x| norm(&to_doc(&x))))).map_err(|_| ());
                let mut ad = to_doc(d);
                let adr = catch_unwind(AssertUnwindSafe(|| a::delete_json_adapted(&mut ad, pb).map(|x| norm(&x)))).map_err(|_| ());
                assert!(rel == adr, "MISMATCH delete {d} {p}: {rel:?} vs {adr:?}");
                assert!(norm(&to_doc(&rv)) == norm(&ad), "MISMATCH delete doc {d} {p}");
                *counts.entry("17 delete (json)").or_default() += 1;
            }
        }
    }
}

pub fn run5(counts: &mut std::collections::BTreeMap<&'static str, u64>) {
    use jsonptr::diagnostic::{Diagnostic, Label};
    use jsonptr::index::{Index, StringOrToken};
    use std::str::FromStr;
    let alpha = ['0', '1', '9', 'a', '-', '+', 'é', '~'];
    let mut strs = vec![String::new()];
    let mut layer = vec![String::new()];
    for _ in 0..5 {
        let mut next = vec![];
        for s in &layer { for c in alpha { let mut t = s.clone(); t.push(c); next.push(t); } }
        strs.extend(next.iter().cloned());
        layer = next;
    }
    for s in &strs {
        if let Err(e) = Index::from_str(s) {
            let rel = catch_unwind(AssertUnwindSafe(|| e.labels(&StringOrToken::from(s.clone())).map(|it| it.collect::<Vec<Label>>()))).map_err(|_| ());
            let ad = catch_unwind(AssertUnwindSafe(|| a::parse_index_error_label_adapted(&pie(&e), s.as_bytes()).map(|sp| {
                let text = match e { ParseIndexError::LeadingZeros => "leading zeros", _ => "invalid character(s)" };
                vec![Label::new(text.to_string(), sp.offset, sp.len)]
            }))).map_err(|_| ());
            assert!(rel == ad, "MISMATCH ParseIndexError::labels {s:?}: {rel:?} vs {ad:?}");
            *counts.entry("19 ParseIndexError::labels").or_default() += 1;
        }
    }
    let origins = ["", "/", "/a", "/a/b", "/ab/", "//"];
    for o in origins {
        let pb = jsonptr::PointerBuf::parse(o).unwrap();
        for pos in [0usize, 1, 2, 3, usize::MAX] {
            for off in [0usize, 1, 2, 3, 4, usize::MAX - 1, usize::MAX] {
                let re = jsonptr::resolve::Error::NotFound { position: pos, offset: off };
                let rel = catch_unwind(AssertUnwindSafe(|| re.labels(&pb).map(|it| it.map(|l| format!("{l:?}")).collect::<Vec<_>>()))).map_err(|_| ());
                let ad = catch_unwind(AssertUnwindSafe(|| a::resolve_error_label_adapted(&ResolveErrorAdapted::NotFound { position: pos, offset: off }, o.as_bytes())
                    .map(|sp| vec![format!("{:?}", Label::new("not found in value".to_string(), sp.offset, sp.len))]))).map_err(|_| ());
                assert!(rel == ad, "MISMATCH resolve labels {o} {pos} {off}: {rel:?} vs {ad:?}");
                *counts.entry("19 resolve::Error::labels").or_default() += 1;
                let ae = jsonptr::assign::Error::FailedToParseIndex { position: pos, offset: off, source: ParseIndexError::LeadingZeros };
                let rel = catch_unwind(AssertUnwindSafe(|| ae.labels(&pb).map(|it| it.map(|l| format!("{l:?}")).collect::<Vec<_>>()))).map_err(|_| ());
                let ad = catch_unwind(AssertUnwindSafe(|| a::assign_error_label_adapted(&AssignErrorAdapted::FailedToParseIndex { position: pos, offset: off, source: ParseIndexErrorAdapted::LeadingZeros }, o.as_bytes())
                    .map(|sp| vec![format!("{:?}", Label::new("expected array index or '-'".to_string(), sp.offset, sp.len))]))).map_err(|_| ());
                assert!(rel == ad, "MISMATCH assign labels {o} {pos} {off}: {rel:?} vs {ad:?}");
                *counts.entry("19 assign::Error::labels").or_default() += 1;
                let rel = (ae.position(), ae.offset(), ae.is_out_of_bounds(), ae.is_failed_to_parse_index());
                let aa = AssignErrorAdapted::FailedToParseIndex { position: pos, offset: off, source: ParseIndexErrorAdapted::LeadingZeros };
                let ad = (a::assign_error_position_adapted(&aa), a::assign_error_offset_adapted(&aa), a::assign_error_is_out_of_bounds_adapted(&aa), a::assign_error_is_failed_to_parse_index_adapted(&aa));
                assert!(rel == ad, "MISMATCH assign accessors");
                *counts.entry("18 assign::Error accessors").or_default() += 1;
            }
        }
    }
    let _ = Value::Null;
}
