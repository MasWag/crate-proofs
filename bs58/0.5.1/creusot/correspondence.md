# Runtime correspondence with bs58 0.5.1

The verification crate contains four implementations selected from the release:
`Alphabet::new` (`bs58/src/alphabet.rs`), `encode_into`
(`bs58/src/encode.rs`), `decode_into`, and `decode_into_const`
(`bs58/src/decode.rs`). The source in `creusot/crate/src/lib.rs` is the proof
fork. It uses the same arithmetic, branch order, errors, alphabet tables, and
write order as the cited release functions. `Alphabet::new` is public in the
release. The three codec helpers are public in this fork so the standalone
crate can exercise them; their release counterparts are private and reached
through public builders.

## Runtime adaptations

| Release | Proof fork | Reason |
| --- | --- | --- |
| `encode_into` accepts `I: Clone + IntoIterator<Item=&u8>` | Takes `&[u8]` | The no-checksum builder calls it with a byte slice. This narrows the verified input domain to slices and does not cover chained checksum iterators. |
| Encoder `for &val in input.clone()` | `while i < input.len()` with `val = input[i]` | Exposes the consumed prefix to loop invariants. The same bytes are processed in order. |
| Encoder `for byte in &mut output[..index]` | `while j < index`, reading and writing `output[j]` | Exposes the digit index; each active digit is updated in the same order. |
| Encoder `(byte as usize) << 8` | `(byte as usize) * 256` | For a byte, the multiplication equals the left shift and fits `usize`; ordinary multiplication exposes the carry equation to the prover. |
| Encoder `input.into_iter().take_while(...)` and `for val in &mut output[..index]` | Index loops | Preserves leading-zero scan, digit substitution, and writes. |
| Encoder and decoder `output[..index].reverse()` | Explicit index-swap loop | Performs the same swaps from the ends toward the center without a slice API model. |
| Decoder `for (i,c) in input.iter().enumerate()` and output iterator | Index loops | Exposes the prefix and digit index while preserving the same validation order and arithmetic. |
| Decoder `output.get_mut(index).ok_or(...)` | Capacity test, then `output[index]` | Produces the same `BufferTooSmall` before a write at the same position. |
| Decoder `val & 0xFF` and `val >>= 8` | `val % 256` and `val /= 256` | For nonnegative `usize`, the bit mask is the low byte and right shift by eight divides by 256; both expressions give the same byte and carry. This exposes ordinary arithmetic to the prover. |
| `decode_into_const` | One macro emits the same body as `const fn` for native Rust and ordinary `fn` under `cfg(creusot)`, with the decoder arithmetic adaptation above | Creusot's checked ghost calls and `snapshot!` cannot be invoked inside Rust `const fn`. The proof checks the fixed-array computation and contract in a runtime context; it does not prove compile-time evaluation semantics. `cfg(creusot)` array copies record proof snapshots and are absent from native builds. |
| `Alphabet::new` | Same original body, apart from the shared fork error type | Preserves earliest non-ASCII or duplicate error and both tables. |
| Original `Clone`, `Copy`, `Debug`, `Eq`, and `PartialEq` derives | Retained in native Rust, omitted only under `cfg(creusot)` | Creusot's `PartialEq` derive requires a `DeepModel` implementation for these fork types. The selected proof does not claim the omitted trait implementations or refinements. |

The fork omits builder targets, checksum paths, display formatting, and
associated alphabet constants from this proof crate. Native differential tests
must compare the selected fork functions through the release's public builders
and include capacity/error precedence, leading zeros, and const-array padding.
Such finite tests support correspondence only for their inputs; they do not
prove equivalence for all inputs. Verification contracts and their evidence
apply to the selected fork functions, not to excluded release APIs.
