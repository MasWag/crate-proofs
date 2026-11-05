# unindent 0.2.4: byte-level functional specification

Specification responsibility: the specification agent, independent of the proof
implementation agent. The primary reviews scope, source identity, commands and
evidence. This document defines obligations; it is not evidence that they hold.

Source basis: crates.io release source
`.work/unindent-0.2.4/src/unindent.rs`, inspected 2026-11-03. Its executable
definitions match the upstream `dtolnay/indoc` `src/unindent.rs` inspected the
same day. Upstream `tests/test_unindent.rs` was also inspected; that test file
is not included in the downloaded crate archive. The source lock, extraction configuration, generated bodies,
theorem inventory and accepted run determine the actual proof scope.

## Independent mathematical semantics

Bytes are natural numbers in `[0, 255]`. A byte string is a finite sequence of
bytes. `LF = 10`, `CR = 13`, `SPACE = 32`, `TAB = 9`; concatenation is `++`, and
`drop(k, x)` removes the first `min(k, |x|)` elements. Indentation whitespace is
exactly `{SPACE, TAB}`. A tab counts as one byte, not a display-column expansion.
No other Unicode or ASCII whitespace belongs to this set.

For a byte string `x`, define `segments(x)` as its decomposition at LF bytes,
retaining every empty field, including the terminal field. It is the unique
nonempty list `[l0, ..., ln]` of LF-free byte strings such that
`x = l0 ++ [LF] ++ ... ++ [LF] ++ ln`. In particular,
`segments([]) = [[]]` and `segments([LF]) = [[], []]`.

Define `prepare(x)` to delete exactly the initial CR byte when `x` begins with
`[CR, LF]`, and otherwise leave `x` unchanged. This special treatment does not
strip CR from subsequent lines. Let `[l0, ..., ln] = segments(prepare(x))`.

A line is *blank* iff all its bytes belong to `{SPACE, TAB}`; the empty line is
blank. A nonblank line's indentation `indent(l)` is the unique number `k` such
that its first `k` bytes are indentation whitespace and its byte at index `k`
is not. Define the eligible set of indentation counts by

`E(x) = { indent(li) | 1 ≤ i ≤ n and li is nonblank }`.

The common margin is `m(x) = min E(x)` when that set is nonempty, and `0`
otherwise. Thus the first line never contributes to the margin, even when it
contains content. All-blank documents have margin zero; the specification does
not silently trim all their whitespace.

Let `t0 = l0` and `ti = drop(m(x), li)` for `i > 0`. Define `starts_empty(x)` to
mean that `x` starts with LF or with CRLF. The public byte transformation `U(x)`
is LF-intercalation of `[t1, ..., tn]` when `starts_empty(x)` holds, and
LF-intercalation of `[t0, ..., tn]` otherwise. The first case has `n ≥ 1`,
so its list is nonempty. LF-intercalation of one empty field is empty.

This specification is a relation on finite byte strings using decomposition,
minimum and concatenation. It must not be replaced by a copy of the generated
loop as the sole functional specification.

## Public contracts

For every input byte slice `x` representable in the Rust execution model,
`unindent_bytes(x)` must terminate successfully with exactly `U(x)`. Prefer a
Lean statement of the form

`∃ out, actual_unindent_bytes input = Result.ok out ∧ out_bytes out = U(input_bytes input)`.

The statement must use the actual extracted function and an explicit relation
between the Rust slice/vector representations and mathematical sequences.
List lengths must obey the actual `usize` and slice representation bounds.
Representability is a boundary condition, not permission to exclude particular
contents or to require positive margin or nonempty input. Record the allocation
model and any ambient resource assumptions separately; an allocator model is
not a proof of operating-system memory availability.

For every valid Rust UTF-8 string `s`, `unindent(s)` must terminate successfully
with a valid UTF-8 string whose encoding is `U(encode(s))`. The successful
`String::from_utf8(...).unwrap()` is part of this obligation, rather than an
assumption that the byte output is valid. A sufficient independent UTF-8 lemma
is that only ASCII indentation prefixes and complete LF/initial-CR bytes are
removed; no UTF-8 continuation byte is removed from a multibyte encoding.

Each extension implementation has the same observable result as its designated
free function: `str` and `String` return the string result; `[u8]` returns the
byte result; `&T` delegates to the underlying `T: Unindent` implementation.
The generic reference theorem can guarantee correct delegation for arbitrary
user implementations, not that arbitrary user implementations equal `U` or
terminate. Its unindent guarantee for built-in types requires the corresponding
base implementation theorem.

## Coverage ledger and proof dependencies

All entries start **unproved**. An extraction attempt, native test, helper proof,
or proposed contract does not change that status. Record accepted theorem names
and limitations in the theorem inventory and report, preserving these entries.

| Operation | Required observable contract | Role |
|---|---|---|
| `unindent_bytes` | Total success and exact `U(x)` for arbitrary bytes | Core public algorithm |
| `unindent` | Total success, UTF-8 closure, bytes equal `U(encode(s))` | Core public algorithm |
| `<str as Unindent>::unindent` | Exact delegation and public string contract | Public extension API |
| `<String as Unindent>::unindent` | Exact delegation and public string contract | Public extension API |
| `<[u8] as Unindent>::unindent` | Exact delegation and public byte contract | Public extension API |
| `<&T as Unindent>::unindent` | Exact delegation; inherited guarantees conditional on `T` | Public generic extension API |
| `count_spaces` | `None` iff blank; otherwise first non-space/tab index | Private helper, no public coverage by itself |
| `BytesExt::lines` | `segments(prepare(x))`, including empty endpoints | Private decomposition helper |
| `do_unindent_bytes` | Core semantics, including its boolean flag if selected | Private core implementation |
| `do_unindent` | Core string semantics and UTF-8 conversion | Private core implementation |

For a generalized private boolean contract, margin and `prepare(x)` stay the
same. `preserve_empty_first_line = true` LF-intercalates all fields `[t0,...,tn]`
even when the input starts with LF/CRLF. In particular this flag does not preserve
the initial CR of CRLF. The public functions always pass `false`.

Useful subordinate obligations are output length `|U(x)| ≤ |x|`, margin no
larger than any nonblank later line's indentation, output order preservation,
safe byte indexing/slicing, and exact preservation of the first line unless it
is the recognized initial empty line. These obligations support the core
contracts but cannot substitute for them. Do not claim idempotence: for example
`U([LF,LF]) = [LF]` whereas `U(U([LF,LF])) = []`.

## Required edge cases

The following are byte literals, so escapes denote exact bytes. They are
specification examples, with native execution status tracked separately.

| Input | `U(input)` | Reason |
|---|---|---|
| `b""` | `b""` | One empty field |
| `b"    a"` | `b"    a"` | First line unchanged |
| `b"\n"` | `b""` | One initial newline removed |
| `b"\n\n"` | `b"\n"` | Only one initial empty line suppressed |
| `b"\r\n"` | `b""` | Initial CRLF suppressed |
| `b"\r"` | `b"\r"` | Lone CR is content |
| `b"\n  a\n    b\n"` | `b"a\n  b\n"` | Common margin and terminal LF |
| `b"prefix\n  a\n    b"` | `b"prefix\na\n  b"` | First line excluded from minimum |
| `b"\n \t"` | `b" \t"` | No nonblank later line gives margin zero |
| `b"\n  a\n \n"` | `b"a\n\n"` | Short blank line drops to empty |
| `b"\n \ta\n\t b"` | `b"a\nb"` | Spaces and tabs each count one |
| `b"\n  \xff\n  x"` | `b"\xff\nx"` | Byte API allows invalid UTF-8 |
| `b"\n  a\r\n  b"` | `b"a\r\nb"` | Later CR retained |
| `b"\r\n    a\r\n\r\n    b"` | `b"    a\r\n\r\n    b"` | Interior CR-only field sets margin zero |

Additional quantified cases include non-ASCII UTF-8 content and whitespace,
embedded NUL, mixtures of LF and CRLF, arbitrarily many consecutive empty lines,
blank lines longer than the common margin, and legal maximum representation
lengths. Concrete tests do not discharge these quantified obligations.

## Candidate behavior discrepancy: blank CRLF lines

The inspected upstream test `carriage_returns` expects preservation of CRLF
between nonempty lines while removing indentation. The implementation recognizes
an initial CRLF, but an interior otherwise empty CRLF line is represented by the
single byte CR. That byte is non-whitespace for margin computation and forces
margin zero. Consequently adding a blank CRLF line can prevent every content
line from being unindented. The analogous LF-only input does not do so.

This is a candidate documentation/behavior discrepancy, not yet a confirmed
upstream bug or a formal counterexample to the exact byte contract above. The
inspected tests do not explicitly promise normalization of blank CRLF lines.
The release-source inspection agrees with this prediction. Native reproduction
must be recorded before reporting it as tested release behavior; a stronger intended line-ending-invariance
property must be justified separately from the implemented semantics.

Minimal native Rust reproduction using `unindent = "=0.2.4"`:

```rust
fn main() {
    let lf = "\n    a\n\n    b";
    let crlf = "\r\n    a\r\n\r\n    b";
    assert_eq!(unindent::unindent(lf), "a\n\nb");
    assert_eq!(unindent::unindent(crlf), "    a\r\n\r\n    b");
    assert_ne!(unindent::unindent(crlf), "a\r\n\r\nb");
}
```

No source adaptation, verifier change, publication or proof success is implied
by this specification. If a required boundary cannot be extracted or proved,
retain the full contract above and record the narrower checked scope separately.
