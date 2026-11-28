use jsonptr::diagnostic::{Diagnostic, Label};
use jsonptr::index::{Index, OutOfBoundsError, ParseIndexError};
use jsonptr::{
    assign, resolve, Diagnose, EncodingError, InvalidEncoding, ParseError, Pointer, PointerBuf,
    Token,
};
use std::ops::Bound;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn strip_prefix_requires_a_token_boundary() {
    let pointer = Pointer::from_static("/ab");
    let prefix = Pointer::from_static("/a");
    assert!(!pointer.starts_with(prefix));

    let remainder = pointer.strip_prefix(prefix).unwrap();
    assert_eq!(remainder.as_str(), "b");
    assert!(Pointer::parse(remainder.as_str()).is_err());

    let escaped = Pointer::from_static("/~0");
    assert_eq!(
        escaped
            .strip_prefix(Pointer::from_static("/"))
            .unwrap()
            .as_str(),
        "~0"
    );
    assert_eq!(
        Pointer::from_static("/a/東京")
            .strip_prefix(prefix)
            .unwrap()
            .as_str(),
        "/東京"
    );
    assert_eq!(prefix.strip_prefix(prefix), Some(Pointer::root()));

    let unicode = Pointer::from_static("/aé").strip_prefix(prefix).unwrap();
    assert_eq!(unicode.as_str(), "é");
    assert!(std::panic::catch_unwind(|| unicode.front()).is_err());
}

#[test]
fn excluded_maximum_bound_overflows() {
    let pointer = Pointer::from_static("/one/two");
    let results = [
        (Bound::Included(0), "/one"),
        (Bound::Excluded(1), "/one"),
        (Bound::Unbounded, "/one/two"),
    ];
    for (end, wrapped) in results {
        let result = std::panic::catch_unwind(|| pointer.get((Bound::Excluded(usize::MAX), end)));
        if cfg!(debug_assertions) {
            assert!(result.is_err());
        } else {
            assert_eq!(result.unwrap().unwrap().as_str(), wrapped);
        }
    }
    assert_eq!(pointer.get(usize::MAX..), None);
    assert_eq!(
        pointer.get((Bound::Excluded(0), Bound::Unbounded)),
        Some(Pointer::from_static("/two"))
    );
}

#[test]
fn terminal_tilde_diagnostic_extends_past_input() {
    for input in ["/~", "/a~", "/é/~", "/a/~"] {
        let error = Pointer::parse(input).unwrap_err();
        assert_eq!(error.complete_offset(), input.len() - 1);
        assert_eq!(error.invalid_encoding_len(input), 2);
    }

    let input = "/a~2";
    let error = Pointer::parse(input).unwrap_err();
    assert_eq!(error.complete_offset(), 2);
    assert_eq!(error.invalid_encoding_len(input), 2);
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    match payload.downcast::<String>() {
        Ok(message) => *message,
        Err(payload) => payload
            .downcast::<&'static str>()
            .map(|message| message.to_string())
            .unwrap_or_default(),
    }
}

fn index_labels(input: &str) -> (ParseIndexError, Option<Vec<Label>>) {
    let report = Index::try_from(input)
        .diagnose(String::from(input))
        .unwrap_err();
    let (error, subject) = report.decompose();
    let labels = error.labels(&subject).map(Iterator::collect);
    (error, labels)
}

#[test]
fn all_zero_index_label_panics() {
    for input in ["00", "000"] {
        let report = Index::try_from(input)
            .diagnose(String::from(input))
            .unwrap_err();
        let (error, subject) = report.decompose();
        assert_eq!(error, ParseIndexError::LeadingZeros);
        let result = catch_unwind(AssertUnwindSafe(|| {
            error.labels(&subject).map(Iterator::count)
        }));
        assert_eq!(panic_message(result.unwrap_err()), "starts with zeros");
    }

    let leading = |len| Some(vec![Label::new("leading zeros".into(), 0, len)]);
    assert_eq!(index_labels("01").1, leading(1));
    assert_eq!(index_labels("0a").1, leading(1));
    assert_eq!(index_labels("000001").1, leading(5));
}

#[test]
fn invalid_character_label_exceeds_subject() {
    let invalid = |offset, len| Some(vec![Label::new("invalid character(s)".into(), offset, len)]);

    let (error, labels) = index_labels("1abc");
    match error {
        ParseIndexError::InvalidCharacter(ref source) => assert_eq!(source.offset(), 1),
        _ => panic!("unexpected error {error:?}"),
    }
    assert_eq!(labels, invalid(1, 4));
    assert!(1 + 4 > "1abc".len());
    assert_eq!(index_labels("1-").1, invalid(1, 2));
    assert_eq!(index_labels("1é").1, invalid(1, 3));

    let input = "aé1";
    assert_eq!(index_labels(input).1, invalid(0, 2));
    assert!(!input.is_char_boundary(2));

    assert_eq!(index_labels("bar").1, invalid(0, 3));
    assert_eq!(index_labels("1a2").1, invalid(1, 1));
}

#[test]
fn diagnostic_urls_name_wrong_pages() {
    let base = "https://docs.rs/jsonptr/0.8.2/jsonptr/";
    assert_eq!(
        <resolve::Error as Diagnostic>::url(),
        format!("{base}assign/enum.Error.html")
    );
    assert_eq!(
        <ParseIndexError as Diagnostic>::url(),
        format!("{base}enum.ParseIndexError.html")
    );
    assert_eq!(
        <ParseError as Diagnostic>::url(),
        format!("{base}struct.ParseError.html")
    );

    assert_eq!(
        <assign::Error as Diagnostic>::url(),
        format!("{base}assign/enum.Error.html")
    );
    assert_eq!(
        <EncodingError as Diagnostic>::url(),
        format!("{base}struct.EncodingError.html")
    );
}

#[test]
fn encoding_error_offset_is_after_tilde() {
    for (input, offset) in [("a~b", 2), ("~", 1), ("~~", 1), ("invalid~tilde", 8)] {
        let error = Token::from_encoded(input).unwrap_err();
        assert_eq!(error.source, InvalidEncoding::Tilde);
        assert_eq!(error.offset, offset);
        assert_eq!(input.find('~').unwrap() + 1, offset);
    }

    let subject = String::from("a~b");
    let error = Token::from_encoded(subject.as_str()).unwrap_err();
    let labels: Vec<_> = error.labels(&subject).unwrap().collect();
    assert_eq!(labels, vec![Label::new("must be 0 or 1".into(), 2, 1)]);

    let error = Pointer::parse("/a~b").unwrap_err();
    assert_eq!(error.pointer_offset(), 0);
    assert_eq!(error.source_offset(), 2);
    assert_eq!(error.complete_offset(), 2);

    let error = Token::from_encoded("a/b").unwrap_err();
    assert_eq!(error.source, InvalidEncoding::Slash);
    assert_eq!(error.offset, 1);
}

#[test]
fn diagnostic_helpers_overflow_on_hand_built_errors() {
    fn check<T: PartialEq + std::fmt::Debug>(op: &str, released: T, f: impl FnOnce() -> T) {
        let result = catch_unwind(AssertUnwindSafe(f));
        if cfg!(debug_assertions) {
            let message = panic_message(result.unwrap_err());
            assert_eq!(message, format!("attempt to {op} with overflow"));
        } else {
            assert_eq!(result.unwrap(), released);
        }
    }

    let tilde = |offset| EncodingError {
        offset,
        source: InvalidEncoding::Tilde,
    };

    let error = ParseError::InvalidEncoding {
        offset: 0,
        source: tilde(1),
    };
    check("subtract", 2, || error.invalid_encoding_len(""));

    let pointer = PointerBuf::parse("/a").unwrap();
    let error = resolve::Error::NotFound {
        position: 0,
        offset: usize::MAX,
    };
    check(
        "add",
        Some(vec![Label::new("not found in value".into(), 0, 1)]),
        || error.labels(&pointer).map(Iterator::collect::<Vec<_>>),
    );

    let error = assign::Error::OutOfBounds {
        position: 0,
        offset: usize::MAX,
        source: OutOfBoundsError {
            length: 0,
            index: 1,
        },
    };
    check(
        "add",
        Some(vec![Label::new("1 is out of bounds (len: 0)".into(), 0, 1)]),
        || error.labels(&pointer).map(Iterator::collect::<Vec<_>>),
    );

    let error = ParseError::InvalidEncoding {
        offset: usize::MAX,
        source: tilde(1),
    };
    check("add", 0, || error.complete_offset());

    let error = tilde(0);
    check(
        "subtract",
        Some(vec![Label::new(
            "incomplete escape sequence".into(),
            usize::MAX,
            1,
        )]),
        || {
            error
                .labels(&String::new())
                .map(Iterator::collect::<Vec<_>>)
        },
    );

    let error = Pointer::parse("/a~").unwrap_err();
    assert_eq!(error.complete_offset(), 2);
    let error = resolve::Error::NotFound {
        position: 0,
        offset: 0,
    };
    assert_eq!(
        error.labels(&pointer).map(Iterator::collect::<Vec<_>>),
        Some(vec![Label::new("not found in value".into(), 1, 1)])
    );
}

fn main() {}
