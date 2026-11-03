# Proof inventory

All four claims are universally quantified over the generated Lean input type,
its Rust `AsRef<[u8]>` model instance, and the supplied alphabet. They refer to
the unmodified Aeneas-generated functions in `proofs/Generated/Bs58.lean`.

| Public Rust API | Lean theorem | Result established |
| --- | --- | --- |
| `encode::EncodeBuilder::new` | `bs58.encode_builder_new_spec` | Returns a builder storing exactly the supplied input and alphabet with `Check.Disabled`. |
| `encode::EncodeBuilder::with_alphabet` | `bs58.encode_builder_with_alphabet_spec` | Returns the existing builder with only its alphabet field replaced. |
| `decode::DecodeBuilder::new` | `bs58.decode_builder_new_spec` | Returns a builder storing exactly the supplied input and alphabet with `Check.Disabled`. |
| `decode::DecodeBuilder::with_alphabet` | `bs58.decode_builder_with_alphabet_spec` | Returns the existing builder with only its alphabet field replaced. |

These establish the explicit-alphabet part of W1 in `SPECIFICATIONS.md`; they
do not establish the default-alphabet `from_input` part of W1. The API input's
trait-model instance is passed but unused by these four generated bodies. The
theorems allow any supplied `Alphabet` structure; they do not assert that its
tables are valid. No other specification obligation in that document is claimed
as proved. In particular, the private `max_encoded_len` was extracted but no
public claim is mapped to it.

Verification: `lake build Proofs` succeeded with 1,799 jobs using the pinned
Lean 4.35.0 Aeneas dependency. `lean-axioms.log` is Lean's `#print axioms` output
for each named theorem: the complete transitive list is exactly `propext`,
`Classical.choice`, and `Quot.sound`. No selected proof or generated source uses
`sorry` or declares a custom axiom. `regeneration.sha256` records identical
hashes across two consecutive exact-toolchain extraction runs.
