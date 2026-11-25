# Functional contracts for toml_write 0.1.2

These are verification targets. The theorem inventory and report identify the targets discharged against extracted Rust. The notation below uses finite sequences, mathematical naturals, and Unicode scalar values. Every input string has a valid Rust UTF-8 representation whose byte length fits the Rust target. An empty string is a valid input everywhere.

## String observations

For a string s and a quote character q, let run(q,s) be the largest n for which n copies of q occur consecutively in s, including zero. Let C be the ASCII controls U+0000 through U+001F together with U+007F. TAB is U+0009 and LF is U+000A. Define these predicates on s.

| Predicate | Definition |
| --- | --- |
| bare | s is nonempty and every scalar is an ASCII letter, decimal digit, hyphen, or underscore |
| keyControl | s contains an element of C other than TAB |
| valueControl | s contains an element of C other than TAB and LF |
| slash | s contains U+005C |
| lf | s contains LF |

Key metrics are exactly bare, presence of apostrophe, presence of double quote, keyControl, and slash. Value metrics are the two maximum run lengths, valueControl, slash, and lf. Exact run lengths in the release's eight-bit fields require both runs to be at most 255. Checked release-source construction on all representable strings is a separate, falsifiable totality target. The encoding decisions below use only thresholds zero and two, so their mathematical domain includes longer runs too.

## Builder results

### Constructor domain and loop invariant

For each quote byte q (39 or 34), let tail(q,p) be the greatest n such that the final n bytes of prefix p all equal q. Let run(q,p) be the greatest tail(q,t) over all prefixes t of p, including the empty prefix. These definitions on bytes agree with the scalar definitions because the UTF-8 encoding of a non-ASCII scalar contains only bytes above 127.

After processing the first i bytes, the two running counters have values tail(q,p), the two stored maxima have values run(q,p), and the three Boolean fields equal valueControl(p), slash(p), and lf(p). For empty p the four counts are zero and all three flags are false. Appending a matching byte increments its tail by one. Appending any other byte resets its tail to zero. The new maximum is the greater of the old maximum and the new tail. For every prefix, both tails are bounded by their corresponding maxima on the full input. Thus the two bounds run(39,s) ≤ 255 and run(34,s) ≤ 255 suffice for every checked increment. Total input length and total quote count may each exceed 255. With those bounds, the constructor must return successfully with the original decoded text and all five specified fields. A run reaching 256 lies outside this success contract and exercises the published counter-overflow defect.

Each successful selection returns the original decoded text. A value carries lf as its newline flag. A key writes with newline flag false. The following equivalences specify both Some and None outcomes.

| Encoding request | Key eligibility | Value eligibility |
| --- | --- | --- |
| Unquoted | bare | No such method |
| Literal | no keyControl and no apostrophe | no valueControl, no apostrophe, and no lf |
| Pretty basic | no keyControl, slash, or double quote | no valueControl, slash, double quote, or lf |
| Pretty multiline basic | No such method | no valueControl or slash, double-quote run at most two |
| Multiline literal | No such method | no valueControl, apostrophe run at most two |
| Basic | always | always |
| Multiline basic | No such method | always |

Key default takes the first eligible choice in the order unquoted, pretty basic, literal, basic. Value default takes the first eligible choice in the order pretty basic, literal, pretty multiline basic, multiline literal. If all four are ineligible it uses multiline basic when lf holds and basic otherwise. Pretty basic selects the same encoding as basic, including escaping TAB. Contracts for selectors on a raw builder may use these decisions directly on its stored flags and counts. Connecting a raw selector theorem to a public constructor requires a separate metrics theorem for the input.

For the default methods, require total success and exact equality of the returned descriptor for every raw builder, including inconsistent cached states. A source adaptation that expands the option combinators must preserve the receiver, the order and laziness of alternative evaluation, each branch's successful descriptor, and short-circuit propagation of any prior failure. Rust `Option::or_else` calls its closure only on `None`; `unwrap_or_else` calls its closure only on `None` and otherwise returns the contained value. Document which of these standard-library observations are assumed and which release or adapted bodies the proof actually checks. For reachable descriptors the key constructor is unconditional and the string constructor has the two quote-run bounds above.

## Exact text written

The reference token consists of opening delimiter, optional LF, encoded body, and closing delimiter. Both delimiters are identical. Bare keys use the empty delimiter. Literal and basic strings use one apostrophe and one double quote respectively. Their multiline variants use three copies. The optional LF occurs exactly for a multiline encoding with the supplied newline flag. Literal and bare bodies are s itself.

In basic bodies, replace each maximal run of n double quotes as a unit. For single-line basic, emit n copies of backslash followed by double quote as two-character pairs. For multiline basic, write n = 3k + r with 0 ≤ r < 3. Emit k copies of the four-character sequence [double quote, double quote, backslash, double quote], followed by r unescaped double quotes. Independently map the remaining scalars using this table.

| Input | Output text |
| --- | --- |
| Backspace, TAB, form feed, carriage return | The two-character escapes `\b`, `\t`, `\f`, `\r` respectively |
| LF | LF for multiline basic, otherwise the two-character escape `\n` |
| Backslash | Two backslashes |
| Any remaining member of C | Backslash and lowercase u followed by exactly four uppercase hexadecimal digits encoding the scalar value, including leading zeros |
| Any other scalar | The scalar itself, preserving its UTF-8 bytes |

For an infallible append sink with initial text p, the target contract is existence of a successful Aeneas result containing Rust Ok and final text p concatenated with the specified token. For a fallible sink the first failed write returns Rust fmt::Error and prevents subsequent writes. Earlier accepted writes and any partial effect of the failing sink operation need not be rolled back. Proving this requires a contract relating the sink operations and Rust formatting to their observable effects. For a general user-defined key/value implementation, its output, termination, and error behavior require explicit hypotheses. The allocating convenience methods return whatever their fresh String accumulated and discard their delegated Rust error.

## Other formatting targets

| Surface | Observable output on successful append |
| --- | --- |
| Punctuation methods | Table and array delimiters are brackets, array-of-tables delimiters are doubled brackets, and inline-table delimiters are braces. The remaining tokens are dot, equals, comma, ASCII space, hash, and LF, according to the named method. |
| Primitive scalars | Booleans use lowercase true or false. Integers use signed or unsigned base-10 digits without padding. char delegates to the single-scalar string contract. |
| Floating point | Preserve the sign of NaN and zero with nan, -nan, 0.0, or -0.0. Infinities use inf or -inf. Finite nonzero values use Rust Display followed by .0 for integral values and plain Display otherwise. The Display operation is a library boundary. |
| Slices, arrays and vectors | Brackets enclose the ordered element outputs separated by comma and one space. The empty result is two adjacent brackets. |
| Maps | Empty maps give adjacent braces. Otherwise place one space inside each brace and join entries by comma and one space. An entry consists of key output, space, equals, space, and value output. Entries follow the actual iterator's order. |
| Forwarders | References, owned strings, borrowed or owned Cow strings, and writer key/value methods preserve the delegated result and effects. |

A successful emitted token and a token's meaning under a specified TOML parser are distinct observations. The exact-output contract does not impose a global document ordering, a common numeric range across parsers, uniqueness of formatted map keys, or a particular hash map iteration order. Source correspondence for adapted loops, generated code, and any assumed library operation must be accounted for separately when attributing a theorem to the published crate.
