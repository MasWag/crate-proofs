# jsonptr 0.8.2 public API inventory

The specification agent derived this inventory from the locked release source
`.work/source/src`, read in full outside the test modules, on 2026-11-27. It lists every
item a user of the crate can call, under all features, with either a contract in
[specification.md](specification.md) or an exclusion class with a reason. Line numbers
refer to the file named in each heading.

Nothing here is a proof status. A row with a contract says what must be proved, not that
it has been.

## Classes

| Class | Meaning |
| --- | --- |
| C §n | Contracted. The theorem is the contract of section n of the specification. |
| F §n | Forwarder. The body only calls the delegate contracted in section n. The delegate's theorem covers the behaviour; the forwarder needs a forwarding theorem where it extracts, and otherwise a correspondence note. |
| R | Added to a C or F row: the intended contract is refuted for the release by the finding named. Report it as refuted. |
| X-EXT | Excluded: the observable behaviour is produced inside an external crate (`serde`, `serde_json`, `toml`, `miette`) or is a value of an external type. |
| X-FMT | Excluded: the output is produced through `core::fmt::Formatter` (`Display`, `Debug`, `to_string`, `format!`), which the verifier does not model. |
| X-CAST | Excluded: the body is an `unsafe` reference, raw-pointer or `Box` cast, or an `unsafe` constructor whose contract is the caller's obligation. The verifier cannot model the cast, and at the byte level nothing remains to state. |
| X-DYN | Excluded: the result is a trait object (`&dyn Error`). |
| X-HASH | Excluded: the sequence of `Hasher` calls made by derived and `str` hashing is an unspecified standard-library detail, generic over the caller's hasher. |
| X-DECL | No behaviour: a trait, type alias, or marker implementation with an empty body. |

`cfg(test)` code, including `arbitrary.rs`, is not public and is not listed.

Extraction-risk notes are provisional guesses about unchanged Aeneas, made from the
default profile's results. They are not findings.

## `pointer.rs` — `Pointer`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `derive(PartialEq, Eq, PartialOrd, Ord)` | 34 | — | C §21 | Unsized `str` newtype; delegates to `str` comparison |
| `derive(Hash)` | 34 | — | X-HASH | — |
| `derive(Debug)` | 34 | — | X-FMT | — |
| `Default for &Pointer` | 39 | — | F §21 → `root` | Cast in `root` |
| `Display` | 44 | — | X-FMT; forwards to `str` formatting, so padding flags apply | Formatter |
| `new_unchecked` (unsafe) | 63 | — | X-CAST | Raw-pointer cast |
| `root` | 68 | — | X-CAST for the cast; the value is the empty pointer (§21) | Raw-pointer cast, `const fn` |
| `parse` | 82 | — | F §13 → target 1; cast X-CAST | `AsRef<str>` generic, closure, cast |
| `from_static` | 104 | — | C §13 (succeeds exactly on valid input; otherwise the documented panic) | `const fn`, `assert!`, cast |
| `as_str` | 110 | — | C §21 | `&str` |
| `to_buf` | 115 | — | C §21 | `String` |
| `tokens` | 120 | — | C §6 | `str::Split` iterator |
| `count` | 128 | — | C §8 | Iterator `count` |
| `is_root` | 133 | — | C §21 | `&str` |
| `to_json_value` | 139 | json | X-EXT | `serde_json::Value` |
| `back`, `last` | 144, 154 | — | C §8; `last` is F → `back` | `rsplit_once`, closure |
| `front`, `first` | 159, 176 | — | C §8; `first` is F → `front` | `split_once`, closures |
| `split_front` | 181 | — | C §6 | `find`, closures, cast |
| `split_at_offset` | 232 | — | C §10 | `str::split_at`, cast |
| `split_at` (deprecated) | 253 | — | F §10 → `split_at_offset` | — |
| `split_back` | 258 | — | C §8 | `rsplit_once`, closure, cast |
| `parent` | 270 | — | C §8 | `rsplit_once`, closure, cast |
| `strip_suffix` | 278 | — | C §11 | `str::strip_suffix`, closure, cast |
| `strip_prefix` | 287 | — | C §11, R (JSONPTR-001) | `str::strip_prefix`, closure, cast |
| `ends_with` | 298 | — | C §11 | `str::ends_with` |
| `starts_with` | 307 | — | C §11 | `str::starts_with`, byte index |
| `get` | 333 | — | F §8, §9 → `PointerIndex::get` | Sealed-trait dispatch |
| `resolve` | 361 | resolve | F §7 → `Resolve::resolve` of the argument's type; conditional on that implementation | Trait generic |
| `resolve_mut` | 388 | resolve | F §15 → `ResolveMut::resolve_mut`; conditional likewise | Trait generic, `&mut` |
| `intersection` | 396 | — | C §11 | `zip` of iterators, closure |
| `delete` | 457 | delete | F §17 → `Delete::delete`; conditional likewise | Trait generic |
| `assign` | 484 | assign | F §16 → `Assign::assign`; conditional likewise | Trait generic, `Into` |
| `components` | 506 | — | C §8 | `Into`, iterator state |
| `with_trailing_token` | 524 | — | C §12 | `impl Into<Token>`, `String` |
| `with_leading_token` | 544 | — | C §12 | `impl Into<Token>`, `String` |
| `concat` | 565 | — | C §12 | `String` |
| `len` | 585 | — | C §21 | `&str` |
| `is_empty` | 599 | — | C §21 | `&str` |
| `into_buf` | 604 | — | X-CAST | `Box` raw-pointer cast |
| `Serialize` | 613 | serde | X-EXT | Generic `Serializer` |
| `Deserialize for &Pointer` | 623 | serde | X-EXT; the visitor calls `parse`, whose decision is target 1 | Visitor, `format!` |
| `miette::SourceCode` for `Pointer`, `&Pointer`, `PointerBuf` | 658 | miette | X-EXT (3 impls) | — |
| `From<&Pointer> for Cow<Pointer>` | 679 | — | C §21 | `Cow` |
| `ToOwned` | 685 | — | F §21 → `to_buf` | — |
| 17 `PartialEq` impls among `Pointer`, `&Pointer`, `PointerBuf`, `str`, `&str`, `String` | 693–783, 1151, 1157 | — | C §21 | `str` equality |
| `AsRef<Pointer>` for `Pointer`, `PointerBuf` | 766, 771 | — | C §21; the `PointerBuf` one goes through `Deref` (X-CAST) | Cast |
| `From<&Pointer> for serde_json::Value` | 790 | json | X-EXT | — |
| `AsRef<str>`, `Borrow<str>`, `AsRef<[u8]>` | 796, 802, 808 | — | C §21 | `&str`, `as_bytes` |
| 15 `PartialOrd` impls among the same types | 814–894 | — | C §21 | `str` comparison |
| `IntoIterator for &Pointer` | 900 | — | F §8 → `tokens` | — |

## `pointer/slice.rs` — `PointerIndex`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `trait PointerIndex` (sealed) | 5 | — | X-DECL | — |
| `get` for `usize` | 14 | — | C §8 | Iterator `nth` |
| `get` for `Range<usize>` | 22 | — | C §9 | `for` over iterator, `from_utf8_unchecked`, cast |
| `get` for `RangeFrom<usize>` | 62 | — | C §9 | Same, `enumerate` |
| `get` for `RangeTo<usize>` | 87 | — | C §9 | Same |
| `get` for `RangeFull` | 120 | — | C §9 | — |
| `get` for `RangeInclusive<usize>` | 128 | — | C §9 | Same, `into_inner` |
| `get` for `RangeToInclusive<usize>` | 166 | — | C §9 | Same |
| `get` for `(Bound<usize>, Bound<usize>)` | 196 | — | C §9, R (JSONPTR-002) | Machine `start + 1`; dispatch to the other forms |

## `pointer.rs` — `PointerBuf`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)` | 914 | — | C §21 (`Default` is §12) | `String` |
| `derive(Hash)` | 914 | — | X-HASH | — |
| `derive(Debug)` | 914 | — | X-FMT | — |
| `root`, `new` | 921, 926 | — | C §12 | `String::new` |
| `new_unchecked` (unsafe) | 934 | — | X-CAST: no body logic; validity is the caller's obligation | — |
| `parse` | 942 | — | C §13 | `impl Into<String>`, `into_report` |
| `from_tokens` | 951 | — | C §12 | Generic `IntoIterator`, `map(Into::into)` |
| `as_ptr` | 961 | — | C §21; goes through `Deref` (X-CAST) | Cast |
| `push_front` | 966 | — | C §12 | `String::insert`, `insert_str` |
| `push_back` | 972 | — | C §12 | `String::push`, `push_str` |
| `pop_back` | 978 | — | C §12 | `rfind`, `split_off` |
| `pop_front` | 990 | — | C §12 | `bool::then` closure, `mem::replace`, `mem::take` |
| `append` | 1007 | — | C §12 | `AsRef` generic, returns `&Self` |
| `replace` | 1022 | — | C §12 | `collect` to `Vec<Token>`, `Cow` |
| `clear` | 1054 | — | C §12 | — |
| `FromStr` | 1059 | — | F §13 → `TryFrom<&str>` | — |
| `Borrow<Pointer>` | 1066 | — | C §21; through `Deref` | Cast |
| `Deref` | 1072 | — | X-CAST; the value is the same bytes (§21) | `new_unchecked` cast |
| `From<PointerBuf> for Box<Pointer>` | 1080 | — | X-CAST | `Box` raw-pointer cast |
| `Deserialize` | 1089 | serde | X-EXT; calls `TryFrom<String>`, whose decision is target 1 | Generic `Deserializer` |
| `Serialize` | 1101 | serde | X-EXT | Generic `Serializer` |
| `From<PointerBuf> for Cow<'static, Pointer>` | 1110 | — | C §21 | `Cow` |
| `From<Token>` | 1116 | — | F §12 → `from_tokens` | — |
| `TryFrom<String>` | 1122 | — | C §13 | `?` on `Result` |
| `From<usize>` | 1130 | — | X-FMT: the token is `usize::to_string`; then F §12 | Formatter |
| `IntoIterator for &PointerBuf` | 1136 | — | F §8 → `tokens` | — |
| `TryFrom<&str>` | 1144 | — | F §13 → `Pointer::parse` then `to_buf` | — |
| `Display` | 1163 | — | X-FMT | Formatter |

## `pointer.rs` — `ParseError`, `ReplaceError`, validation

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `ParseError`: `derive(PartialEq)` | 1170 | — | C §21 | May extract unchanged |
| `ParseError`: `derive(Debug)` | 1170 | — | X-FMT | — |
| `offset` | 1189 | — | C §18 | May extract unchanged |
| `invalid_encoding_len` | 1196 | — | C §19, R (JSONPTR-003, N5) | `&str` argument for its length only |
| `Diagnostic::url` | 1213 | — | C §19 | `&'static str` constant |
| `Diagnostic::labels` | 1217 | — | C §19, R (JSONPTR-003) | `Box<dyn Iterator>`, `String` |
| `miette::Diagnostic` | 1230 | miette | X-EXT (empty impl, default methods) | — |
| `Display` | 1232 | — | X-FMT | — |
| `is_no_leading_backslash` (deprecated), `is_no_leading_slash`, `is_invalid_encoding` | 1254, 1259, 1264 | — | C §18 | May extract unchanged |
| `pointer_offset`, `source_offset` | 1280, 1300 | — | C §18 | May extract unchanged |
| `complete_offset` | 1318 | — | C §18, R for total success (N7) | Machine addition |
| `std::error::Error::source` | 1324 | std | X-DYN | — |
| `type RichParseError` | 1334 | — | X-DECL | — |
| `ReplaceError`: public fields, `derive(PartialEq, Eq)` | 1338 | — | C §21 | May extract unchanged |
| `ReplaceError`: `derive(Debug)`, `Display` | 1338, 1346 | — | X-FMT | — |
| `ReplaceError`: `std::error::Error` | 1353 | std | X-DECL | — |
| `validate` (private; behind every parse) | 1355 | — | C §1 | `str::as_bytes` |
| `validate_bytes` (private) | 1370 | — | default profile, closed | Extracts |

## `token.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `Token`: `derive(Clone, PartialEq, Eq, PartialOrd, Ord)` | 39 | — | C §14, §21 | `Cow<str>` |
| `Token`: `derive(Hash)` | 39 | — | X-HASH | — |
| `Token`: `derive(Debug)` | 39 | — | X-FMT | — |
| `from_encoded` | 77 | — | C §4 | `Cow`, `bytes().enumerate()` |
| `new` | 128 | — | C §2 | `Cow`, `position` closure, `from_utf8_unchecked` |
| `into_owned`, `to_owned` | 169, 182 | — | C §14 | `Cow` |
| `encoded` | 196 | — | C §14 | `&str` |
| `into_encoded` | 212 | — | C §14 | `Cow` |
| `decoded` | 224 | — | C §3 | `Cow`, `position` closure, `from_utf8_unchecked` |
| `to_index` | 283 | — | F §5 → `Index::from_str` via `TryFrom<&Token>` | — |
| `is_next` | 290 | — | C §14 | `matches!` on a `Result` |
| `From<{u8,…,isize}>` (12 impls) | 298 | — | X-FMT: the body is integer `to_string` plus an unchecked wrap | Formatter |
| `From<&str>`, `From<&String>`, `From<String>` | 309, 315, 321 | — | F §14 → target 2 | — |
| `From<&Token>` | 327 | — | C §14 | `Cow` clone |
| `Display` | 333 | — | X-FMT; writes the decoded text | Formatter |
| `Tokens`: `derive(Debug)` | 350 | — | X-FMT | — |
| `Tokens::next` | 357 | — | C §8 | `str::Split`, closure |
| `type InvalidEncodingError` (deprecated) | 382 | — | X-DECL | — |
| `EncodingError`: public fields, `derive(PartialEq, Eq)` | 397 | — | C §21 | May extract unchanged |
| `EncodingError`: `derive(Debug)`, `Display` | 397, 405 | — | X-FMT | — |
| `EncodingError`: `Diagnostic::url` | 418 | — | C §19 | `&'static str` constant |
| `EncodingError`: `Diagnostic::labels` | 422 | — | C §19, R for total success (N8) | `Box<dyn Iterator>`, `String` |
| `EncodingError`: `miette::Diagnostic` | 438 | miette | X-EXT | — |
| `EncodingError`: `std::error::Error::source` | 441 | std | X-DYN | — |
| `InvalidEncoding`: `derive(PartialEq, Eq, Clone, Copy)` | 458 | — | C §21 | May extract unchanged |
| `InvalidEncoding`: `derive(Debug)`, `Display` | 458, 466 | — | X-FMT | — |
| `InvalidEncoding`: `std::error::Error` | 476 | std | X-DECL | — |

## `index.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `Index`: `derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)` | 49 | — | C §21 | May extract unchanged |
| `Index`: `derive(Hash)` | 49 | — | X-HASH | — |
| `Index`: `derive(Debug)` | 49 | — | X-FMT | — |
| `for_len`, `for_len_incl`, `for_len_unchecked` | 81, 114, 140 | — | default profile, closed | Extract |
| `Display` | 148 | — | X-FMT | Formatter |
| `From<usize>` | 157 | — | C §14 | May extract unchanged |
| `FromStr::from_str` | 166 | — | C §5 | `str` patterns, closures, `parse` |
| `TryFrom<&Token>`, `TryFrom<Token>` | 191, 207 | — | F §14 → target 5 | — |
| `TryFrom<&str>`, `TryFrom<String>`, `TryFrom<&String>` | 199, 218 | — | F §14 → target 5 | — |
| `OutOfBoundsError`: public fields, `derive(Clone, PartialEq, Eq)` | 242 | — | C §21 | May extract unchanged |
| `OutOfBoundsError`: `derive(Debug)`, `Display` | 242, 257 | — | X-FMT | — |
| `OutOfBoundsError`: `std::error::Error` | 268 | std | X-DECL | — |
| `ParseIndexError`: `derive(Clone, PartialEq, Eq)` | 281 | — | C §21 for the kind; the `ParseIntError` payload is standard-library data | `ParseIntError` |
| `ParseIndexError`: `derive(Debug)`, `Display` | 281, 297 | — | X-FMT | — |
| `From<ParseIntError>` | 291 | — | C §5 (wraps as `InvalidInteger`) | `ParseIntError` is opaque |
| `StringOrToken` (doc-hidden): `From<String>`, `From<Token>`, `Deref` | 322, 328, 334 | — | C §14 | `String`, `&str` |
| `StringOrToken`: `derive(Debug)` | 316 | — | X-FMT | — |
| `StringOrToken`: `miette::SourceCode` | 346 | miette | X-EXT | — |
| `ParseIndexError`: `Diagnostic::url` | 361 | — | C §19 | `&'static str` constant |
| `ParseIndexError`: `Diagnostic::labels` | 365 | — | C §19, R (N1, N2) | `chars()` closures, `expect`, `Box<dyn Iterator>` |
| `ParseIndexError`: `miette::Diagnostic` | 394 | miette | X-EXT | — |
| `ParseIndexError`: `std::error::Error::source` | 397 | std | X-DYN | — |
| `InvalidCharacterError`: `derive(Clone, PartialEq, Eq)` | 408 | — | C §21 | May extract unchanged |
| `InvalidCharacterError::offset` | 417 | — | C §14 | May extract unchanged |
| `InvalidCharacterError`: `derive(Debug)`, `Display` | 408, 422 | — | X-FMT | — |
| `InvalidCharacterError`: `std::error::Error` | 433 | std | X-DECL | — |

## `component.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `Component`: `derive(PartialEq, Eq, PartialOrd, Ord)` | 4 | — | C §21 | `Token` holds a `Cow<str>` |
| `Component`: `derive(Debug)` | 4 | — | X-FMT | — |
| `From<Token> for Component` | 11 | — | C §8 | — |
| `Components`: `derive(Debug)` | 18 | — | X-FMT | — |
| `Components::next` | 26 | — | C §8 | Holds a `Tokens` iterator; `map` |
| `From<&Pointer> for Components` | 35 | — | C §8 | — |

## `resolve.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `trait Resolve`, `trait ResolveMut` | 49, 66 | resolve | X-DECL | — |
| `type ResolveError` (deprecated) | 84 | resolve | X-DECL | — |
| `Error`: `derive(PartialEq, Eq)` | 87 | resolve | C §21 | `ParseIntError` inside `ParseIndexError` |
| `Error`: `derive(Debug)`, `Display` | 87, 238 | resolve | X-FMT | — |
| `offset`, `position` | 168, 178 | resolve | C §18 | May extract unchanged |
| `is_unreachable`, `is_not_found`, `is_out_of_bounds`, `is_failed_to_parse_index` | 189–207 | resolve | C §18 | May extract unchanged |
| `Diagnostic::url` | 215 | resolve | C §19, R (N3) | `&'static str` constant |
| `Diagnostic::labels` | 219 | resolve | C §19, R for total success (N6); text of `OutOfBounds` is X-FMT | `Box<dyn Iterator>`, `to_string` |
| `std::error::Error::source` | 265 | resolve, std | X-DYN | — |
| `Resolve for serde_json::Value` | 283 | resolve, json | C §7 on the local document type; the `serde_json` instance itself is X-EXT | `while let` over `split_front`, closures, external types |
| `ResolveMut for serde_json::Value` | 325 | resolve, json | C §15 likewise | Same, reborrow of `&mut` in a loop |
| `parse_index` (private helper of the above) | 352 | resolve, json | C §15 (part of it) | Closures |
| `Resolve for toml::Value` | 383 | resolve, toml | C §7 likewise; X-EXT for the instance | Same as JSON |
| `ResolveMut for toml::Value` | 425 | resolve, toml | C §15 likewise | Same as JSON |

## `assign.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `trait Assign` | 110 | assign | X-DECL | — |
| `type AssignError` (deprecated) | 129 | assign | X-DECL | — |
| `Error`: `derive(PartialEq, Eq)` | 134 | assign | C §21 | `ParseIntError` inside |
| `Error`: `derive(Debug)`, `Display` | 134, 194 | assign | X-FMT | — |
| `position`, `offset` | 163, 171 | assign | C §18 | May extract unchanged |
| `is_out_of_bounds`, `is_failed_to_parse_index` | 181, 189 | assign | C §18 | May extract unchanged |
| `Diagnostic::url` | 214 | assign | C §19 | `&'static str` constant |
| `Diagnostic::labels` | 218 | assign | C §19, R for total success (N6); text of `OutOfBounds` is X-FMT | `Box<dyn Iterator>`, `format!` |
| `miette::Diagnostic` | 239 | assign, miette | X-EXT | — |
| `std::error::Error::source` | 246 | assign, std | X-DYN | — |
| `Assign for serde_json::Value` with `expand`, `assign_value`, `assign_array`, `assign_object`, `assign_scalar` | 267–428 | assign, json | C §16 on the local document type; X-EXT for the instance | `Map::entry`, `&mut` handed between loop iterations through an enum, `mem::replace`, closures, `to_string` for keys |
| `Assign for toml::Value` with the same helpers | 439–598 | assign, toml | C §16 likewise | Same |

## `delete.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `trait Delete` | 71 | delete | X-DECL | — |
| `Delete for serde_json::Value` | 98 | delete, json | C §17 on the local document type; X-EXT for the instance | `let … else`, closure with `?`, `Map::remove`, `Vec::remove` |
| `Delete for toml::Value` | 136 | delete, toml | C §17 likewise, with an empty table as root replacement | Same |

## `diagnostic.rs`

| Item | Line | Feature | Class | Extraction risk |
| --- | --- | --- | --- | --- |
| `trait Diagnostic` (declares `url`, `labels`) | 8 | — | X-DECL | — |
| `Diagnostic::into_report` (default method) | 13 | — | C §20 | Trait generic, `impl Into` |
| `Label`: `derive(PartialEq, Eq, Clone)` | 25 | — | C §21 | `String` field |
| `Label`: `derive(Debug)` | 25 | — | X-FMT | — |
| `Label::new` | 37 | — | C §19 | `String` |
| `From<Label> for miette::LabeledSpan` | 43 | miette | X-EXT | — |
| `Report`: `derive(Clone)` | 60 | — | C §21 | Trait-generic struct |
| `Report`: `derive(Debug)` | 60 | — | X-FMT | — |
| `Report::subject`, `original`, `decompose`, `into_original` | 72–87 | — | C §20 | Associated type `Subject: Deref` |
| `Deref for Report` | 92 | — | C §20 | — |
| `Display for Report` | 100 | — | X-FMT | — |
| `std::error::Error for Report` (`source`) | 107 | std | X-DYN | — |
| `miette::Diagnostic for Report` (`url`, `source_code`, `labels`) | 118 | miette | X-EXT; `labels` calls the crate's `labels` (§19) and converts each item | Trait objects |
| `trait Diagnose` (sealed) | 168 | — | X-DECL | — |
| `Diagnose for Result`: `diagnose` | 213 | — | C §20 | `map_err` closure, generics |
| `Diagnose for Result`: `diagnose_with` | 220 | — | C §20 | `FnOnce` parameter, closure |

## `lib.rs`

Re-exports only: `Assign`, `Delete`, `Resolve`, `ResolveMut`, `Diagnose`, `Report`,
`ParseError`, `Pointer`, `PointerBuf`, `ReplaceError`, `RichParseError`, `EncodingError`,
`InvalidEncoding`, `Token`, `Tokens`, `InvalidEncodingError`, `Component`, `Components`,
and the modules `assign`, `delete`, `resolve`, `diagnostic`, `index`. No behaviour.

## Refuted contracts at a glance

| Item | Section | Finding | Kind |
| --- | --- | --- | --- |
| `Pointer::strip_prefix` | 11 | JSONPTR-001 | Wrong result on valid arguments |
| `get` for `(Bound, Bound)` | 9 | JSONPTR-002 | Overflow, wrong result |
| `ParseError::invalid_encoding_len`, `ParseError::labels` | 19 | JSONPTR-003 | Span past the subject |
| `ParseIndexError::labels` | 19 | N1, N2 | Panic; wrong span |
| `resolve::Error::url` | 19 | N3 | Wrong constant |
| `ParseError::invalid_encoding_len` on an empty subject | 19 | N5 | Underflow; hand-built input only |
| `resolve::Error::labels`, `assign::Error::labels` at `offset = usize::MAX` | 19 | N6 | Overflow; hand-built input only |
| `ParseError::complete_offset` | 18 | N7 | Overflow; hand-built input only |
| `EncodingError::labels` at offset 0 on an empty subject | 19 | N8 | Underflow; hand-built input only |

N4 is a documentation defect and refutes no contract: the specification keeps the
release value.
