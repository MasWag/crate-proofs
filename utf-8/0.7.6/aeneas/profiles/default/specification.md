# UTF-8 decoding contracts for utf-8 0.7.6

GPT-6.2 Astra designed the specification. GPT-6.2 Sol began target setup, and GPT-6.1 Sol implemented the Lean proofs. It states proof obligations. The theorem inventory and verification results identify which obligations have machine-checked proofs.

## Byte language and observations

A code word encodes one Unicode scalar, a natural number in 0..D7FF or E000..10FFFF (hexadecimal). The octets of a code word belong to one of the following rows. Each interval includes both endpoints. T denotes 80..BF.

| First byte | Following bytes |
| --- | --- |
| 00..7F | empty |
| C2..DF | T |
| E0 | A0..BF, T |
| E1..EC or EE..EF | T, T |
| ED | 80..9F, T |
| F0 | 90..BF, T, T |
| F1..F3 | T, T, T |
| F4 | 80..8F, T, T |

Read the low 7, 5, 4 or 3 bits of the lead byte for lengths 1, 2, 3 or 4 respectively. Append the low six bits of each following byte to obtain the scalar. Text is a concatenation of zero or more code words. A pending prefix is a nonempty proper prefix of one code word, so its length is 1..3. These definitions include noncharacters such as U+10FFFF.

For any finite byte list X, let V be its longest prefix that is text, and let S be the suffix following V. The first decoding event is defined by these disjoint cases.

* If S is empty, X is valid.
* If S is a pending prefix, X ends with an incomplete scalar.
* Otherwise take the longest prefix I of S that is a pending prefix. If none exists, take the first byte of S as I. The invalid subpart is I and the remaining input R satisfies X = V ++ I ++ R. A byte that prevented extending a pending prefix stays in R.

In particular, E0 80 produces two invalid subparts. E1 80 41 produces one invalid subpart E1 80 followed by the valid byte 41. For an EOF-aware lossy decode, emit V verbatim, emit U+FFFD for each invalid subpart and restart at R. At EOF, emit one U+FFFD for a final pending prefix. Before EOF retain that prefix.

For total-success obligations, the generated Aeneas function must return an outer Result.ok with the specified public observation, including Rust Err and None outcomes. Byte equality of returned strings includes their complete length. For mutable borrows observe the post-state after the borrow ends. Slice origins and offsets are specified at the Rust API level even where the Lean value model observes only contents.

## One-shot decoding and storage

* **decode(X)** accepts every Rust byte slice, including the empty slice. For valid X, return Ok with X as text. For incomplete X, return Incomplete with V as text and a buffer containing S followed by zeros, with length |S|. Otherwise return Invalid with the three contiguous slices V, I and R in their original order. Every unchecked string construction must receive text.
* **Incomplete::empty()** returns four zero bytes and length zero.
* **Incomplete::is_empty()** returns precisely whether the length field is zero for every representable state, including raw lengths 5..255.
* **Incomplete::new(B)** succeeds for any bytes of length at most four, storing B followed by zeros and its exact length. At lengths greater than four, the release's destination slice bounds check fails.
* **Incomplete::take_buffer()** on any length n at most four returns the first n stored bytes, resets the length to zero, and preserves all four buffer bytes. It is a private helper.

## Incremental completion

Let n be the old length, B the full four-byte buffer, P its first n bytes, and X the newly supplied bytes. Assume initially n ≤ 4. Let K be the first min(4 − n, |X|) bytes of X. Overwrite that many bytes starting at n in B with K to obtain B'. Its first n + |K| bytes form W = P ++ K. This specifies the observable buffer bytes even when the operation subsequently reports consuming fewer than |K| bytes.

Choose the result class and retained length m by the first decoding event of W.

| Condition | Class | m |
| --- | --- | --- |
| W is text, including empty | valid | length of W |
| W has a nonempty valid prefix V before an error or pending suffix | valid | length of V |
| W is a pending prefix | pending | length of W |
| W begins with an invalid subpart I | invalid | length of I |

* **try_complete_offsets** succeeds on the exact raw domain m ≥ n and n ≤ 4. It stores (B', m) and returns (m − n, tag), where tag is Some(Ok(())), None or Some(Err(())) for valid, pending or invalid respectively. Lengths above four fail the starting slice bound. For bounded states with m < n, subtracting n from m fails the checked subtraction and the subsequent unwrap panics.
* **try_complete** has the same success domain. For pending it returns None and stores (B', m). For valid or invalid it returns Some with the first m bytes of B' as text or error bytes respectively, and the suffix of X starting at m − n. It leaves (B', 0) after the borrow. Returned data may include multiple valid scalars. When n = 0 and X is empty the return is Some((Ok(""), empty)).
* **Stream invariant.** Empty P or a pending prefix P implies m ≥ n for every X. In the latter case there can be no complete scalar strictly inside P, and every prefix of P shorter than n can still extend using P itself. A pending result therefore consumes all supplied input and leaves a pending prefix for the next call. A completed result may leave the byte that diagnosed a malformed sequence for the next decode step. The invariant permits arbitrary bytes in the unused tail of B.

The public fields and constructor allow a wider domain than the states emitted by decode. For example, Incomplete::new(&[0x61, 0xff]).try_complete(&[]) and Incomplete::new(&[0xff, 0xff]).try_complete(&[]) both panic in the release. They witness the valid-prefix and invalid-subpart branches of the same implicit state precondition. The documented decode-to-try_complete workflow supplies a pending prefix.

## Streaming consumers

* **LossyDecoder::new, feed, Drop.** Given a callback that returns normally, after any finite sequence of chunks the concatenated strings delivered equal the pre-EOF lossy decode of their concatenation. The retained bytes are exactly the final pending prefix, if any. Dropping delivers U+FFFD once when pending, and emits nothing otherwise. This contract concerns concatenated text, permits empty callbacks and does not constrain the grouping of adjacent valid strings.
* **BufReadDecoder::new, next_strict.** For a finite stream with stable unread bytes across successful fill_buf calls and lawful consume behavior, successive results preserve input order, grouping adjacent code words into valid strings and reporting each invalid subpart once with its original bytes. A pending prefix at EOF yields one invalid event before None. The logical input position includes bytes marked for delayed consumption by the wrapper. An I/O error encountered by fill_buf is returned as an I/O error. If retry after a transient error is required, the first subsequent successful result should resume at the first undelivered byte. This stronger property fails for a custom reader that returns a byte, reports an interruption on the second fill, and preserves that unread byte. The wrapper schedules consumption before the second fill and consumes the undelivered byte when retried. The crate documents propagation of I/O errors without specifying post-error recovery.
* **BufReadDecoderError::lossy, next_lossy, read_to_string_lossy.** The error conversion maps an invalid byte sequence to the single replacement character and preserves an I/O error. Under successful reads, concatenating next_lossy outputs, or collecting with read_to_string_lossy, yields the EOF-aware lossy decode. A terminating I/O error propagates from collection. These consumer contracts assume returning callbacks and I/O operations and successful allocation where required.
* Formatting, derived traits, error-source accessors, and the standard library's implementations of UTF-8 validation, unchecked conversion and I/O require separate coverage accounting. An assumed standard-library transition cannot establish the scalar-byte grammar above.

## Additional release methods and observable contracts

These obligations cover the remaining explicitly implemented methods and derive-generated methods in the three release source files. Trait defaults and blanket implementations supplied by Rust's standard library are distinguished from release-authored and derive-generated bodies. The two Copy implementations are marker declarations. The empty Error implementation for DecodeError uses the standard defaults, including source returning None.

### Initial state, cloning and finalization

* LossyDecoder::new(f) returns a decoder with the original callback value f, the four-byte zero array and stored length zero. Construction never invokes f. No hypothesis about calls to f is needed.
* BufReadDecoder::new(r) returns a decoder with the original reader value r, delayed consumption zero, four zero bytes and stored length zero. Construction performs no I/O.
* Incomplete::clone returns a value equal in both fields to its input. Quantify over all possible bytes and all 256 stored lengths.
* DecodeError::clone preserves its variant and every field. For Invalid this includes the complete original valid prefix, error slice, and remaining slice. For Incomplete this includes the valid prefix and all four buffer bytes and the raw length, even for manually built states. Shared-reference fields in the Rust result borrow the original referents. A value-based Lean theorem need only claim content equality unless reference identity is modeled.
* LossyDecoder::drop on any raw state whose stored length is zero makes no callback. For every positive raw length, it invokes the callback exactly once with the one-scalar text U+FFFD (bytes EF BF BD). The buffer contents do not affect this decision. For a callback returning normally, final callback state is that yielded by precisely these calls. Any callback effects or failure at the Rust boundary follow the callback's own behavior. A proof about an explicit drop body must be distinguished from automatic destructor scheduling at Rust scope exit.

### Errors and reader adaptors

* BufReadDecoderError::lossy returns Ok with the replacement character for any InvalidByteSequence payload, even an empty slice or bytes that happen to form text. For Io(e) it returns Err with the original e unchanged. UTF-8 validity and successful I/O are unnecessary preconditions. The constant REPLACEMENT_CHARACTER is exactly one U+FFFD.
* BufReadDecoderError::source returns None for any InvalidByteSequence and Some of the same borrowed inner I/O error for Io(e). Equality of the option tag or of an error-kind code is insufficient to establish the identity of the source.
* Each call to next_lossy has the same reader effects and mutable state transition as one call to next_strict. It preserves EOF, successful text, and I/O errors, and maps each InvalidByteSequence to the replacement text. This single-step contract is distinct from whole-stream correctness.
* For read_to_string_lossy, append the successful text of each such step in order until EOF, returning the resulting string. At the first I/O error return that error without a partial string. Termination and total-success claims require a finite stream, returning reader operations, and successful allocation. Constructor results alone give no loop invariant.

### Diagnostic text

Use a text sink whose successful writes append their input to an observable sequence. Ordinary rendering below assumes every write succeeds, default outer formatting, and successful rendering by any nested user error. A fallible formatter must propagate an encountered formatting failure; a partially written prefix may have reached the sink. The return value alone does not specify the text. Byte counts use the UTF-8 length of a string, independent of its scalar count.

Let Hex(B) be square brackets surrounding the bytes in order as lowercase, two-digit hexadecimal, separated by comma and space. Let H(b) be one such byte without brackets, and Dec(n) be the ordinary decimal numeral.

| Display case | Required text; concatenate the indicated pieces |
| --- | --- |
| DecodeError::Invalid(V,I,R) | `found invalid byte sequence ` + Hex(I) + ` after ` + Dec(length in bytes of V) + ` valid bytes, followed by ` + Dec(length of R) + ` more unprocessed bytes` |
| DecodeError::Incomplete(V,state) | `found incomplete byte sequence Incomplete { buffer: ` + Hex(all four bytes) + `, buffer_len: ` + H(raw length) + ` } after ` + Dec(length in bytes of V) + ` bytes` |
| BufReadDecoderError::InvalidByteSequence(B) | `invalid byte sequence: ` + Hex(B) |
| BufReadDecoderError::Io(e) | `underlying bytestream error: ` + the Display rendering of e |

For the three derived Debug implementations, use Rust's struct or enum constructor spelling, the declared fields in release order, and recursive Debug formatting of each field, including escape handling in strings, every array/slice element, and the wrapped I/O error's Debug behavior. Ordinary Debug rendering of Incomplete with buffer [226,0,0,0] and length 1 is `Incomplete { buffer: [226, 0, 0, 0], buffer_len: 1 }`. DecodeError formats its named variant as Invalid or Incomplete, followed by its fields inside braces. BufReadDecoderError formats its tuple variant as InvalidByteSequence(...) or Io(...). Alternate, width and hexadecimal debug formatting require the appropriate formatter settings and nested behavior. Claims about ordinary formatting should state that scope.

### Boundaries for a release-derived core

The std UTF-8 oracle, string conversion, callbacks and I/O have different observables. The following splits allow internal byte logic to be verified while keeping the remaining release correspondence visible.

* Factor the partition after validation into a function taking a byte slice and a classification (all text, first invalid subpart with offsets, or pending with prefix offset). Prove exact slice contents and delayed state for every classification satisfying the byte-language definition above. A separate proof must identify the validator's result with that definition. Mapping valid byte slices into Rust strings requires an explicit string representation/cast correspondence.
* Factor the four-byte splice and the offsets decision into byte operations before string materialization. Preserve copying into the full public buffer, including bytes beyond the reported consumption. Prove that the normalized decisions agree with the original branch schedule (positive valid prefix first), that every pending state meets the subtraction bound, and that manually built states can reach the checked-subtraction failure. Leave any unproved correspondence to the original std error projections visible.
* Separate stream state transitions from borrowed callbacks or readers only with a trace relation covering emitted strings, empty callbacks when part of the stated observation, order of effects, suffix positions and delayed consumption. For reading, keep the two separate fallible fill operations of the release. Replacing those operations by one read changes the observed response to interruption. Whole-stream correctness also requires progress on invalid subparts and preservation of pending prefixes across chunk boundaries.

### Literal correspondence check

The release's Rust Unicode escape denotes U+FFFD. In the direct Drop extraction at the pinned revisions, Aeneas printed the Lean literal `"\239\191\189"`. Lean 4.35.0 reports `invalid escape sequence` at the first escape. Consequently the direct extraction does not give this constant a Lean meaning. Neither a callback theorem parameterized by arbitrary text nor a theorem conditional on an opaque replacement establishes the U+FFFD literal correspondence.
