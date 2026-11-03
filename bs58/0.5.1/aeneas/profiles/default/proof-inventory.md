# Proof inventory

All four claims are universally quantified over the generated Lean input type,
its Rust `AsRef<[u8]>` model instance, and the supplied alphabet. They refer to
the unmodified Aeneas-generated functions in `proofs/Generated/x86_64-unknown-linux-gnu/Bs58.lean`.

| Public Rust API | Lean theorem | Result established |
| --- | --- | --- |
| `encode::EncodeBuilder::new` | `bs58.encode_builder_new_spec` | Returns a builder storing exactly the supplied input and alphabet with `Check.Disabled`. |
| `encode::EncodeBuilder::with_alphabet` | `bs58.encode_builder_with_alphabet_spec` | Returns the existing builder with only its alphabet field replaced. |
| `decode::DecodeBuilder::new` | `bs58.decode_builder_new_spec` | Returns a builder storing exactly the supplied input and alphabet with `Check.Disabled`. |
| `decode::DecodeBuilder::with_alphabet` | `bs58.decode_builder_with_alphabet_spec` | Returns the existing builder with only its alphabet field replaced. |

These establish the explicit-alphabet part of W1 in `specification.md`; they
do not establish the default-alphabet `from_input` part of W1. The API input's
trait-model instance is passed but unused by these four generated bodies. The
theorems allow any supplied `Alphabet` structure; they do not assert that its
tables are valid. No other specification obligation in that document is claimed
as proved. In particular, the private `max_encoded_len` was extracted but no
public claim is mapped to it.

Initial exploratory Lean build and named axiom prints passed before managed integration. The accepted managed run, if any, is recorded in `results.md` and `evidence/summary.json`; it must freshly regenerate the managed model and recheck the theorem audit.
