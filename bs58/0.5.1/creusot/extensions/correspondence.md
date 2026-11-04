# Correspondence of the additional proof adapters

This independent workspace extends the Rust verification fork. It preserves the
original accepted workspace and its evidence. These are application adaptations,
not proofs of the unchanged release or a formal release-to-fork equivalence.
The exact accepted target inventory and remaining obligations belong in the
extension results, not in this source-correspondence document.

The reference is the same pinned bs58 0.5.1 registry distribution. The four core
bodies and their specifications/helpers were copied into `extensions/crate` from
the accepted core workspace. The original [correspondence](../correspondence.md)
continues to describe those arithmetic and iteration adaptations. Additional
modules compose those bodies through their checked contracts. No application
computation, callback law, or arithmetic lemma may be trusted.

## Builders and concrete fixed-size targets

`wrappers::EncodeBuilder` and `wrappers::DecodeBuilder` retain explicit input,
alphabet, and disabled-check state. The extension targets disabled checking;
the release's enabled checksum variants and their state setters are separate
obligations. Generic constructors store their input without calling `AsRef`.
Codec methods specialize input to byte slices, so no stability law is assumed
for arbitrary `AsRef` implementations.

The slice `onto` adapters retain maximum-length calculation and callback dispatch
through the provided target implementations. The slice/array target calls the
callback on the complete original mutable byte slice and propagates its return
value and modifications. Reference forwarding has its own checked contracts and
generated refinements. The proof-only target observation and callback premises
describe this restricted concrete target domain; they do not impose behavior on
every legal implementation of the original public target traits.

`DecodeBuilder::onto_array` names the release's array-target specialization
explicitly. It writes into an existing array and preserves an unused successful
suffix. This differs from `into_array_const`, which creates a zero-initialized
array and returns a padded result. The latter's proof checks the adapted runtime
computation, not Rust compiler constant-evaluation semantics. Any unwrap wrapper
needs its stated success precondition because errors deliberately panic.

The length helper evaluates the release expression `n + (n + 1) / 2`. Its exact
machine-arithmetic contract and the separate mathematical theorem that this is a
sufficient output capacity must not be conflated.

`defaults.rs` retains the actual associated BITCOIN, MONERO, RIPPLE, FLICKR and
DEFAULT constants. Byte-string literals are replaced by equal numeric byte-array
literals because the installed translator cannot lower the relevant byte-string
term. The constant initializer obligations themselves are selected. MONERO has
the same table values as BITCOIN; no pointer-identity claim follows. DEFAULT is
defined through BITCOIN. The crate-private `from_input` helpers delegate to the
checked `new(input, Alphabet::DEFAULT)` instead of repeating the three field
initializers; top-level `encode` and `decode` retain the `from_input` call.

`checked_state.rs` is a separate state-only projection of builders with both
checksum features enabled. It retains the three Check variants and copies the
constructors, alphabet replacement, and version/mode setter bodies. These proofs
establish exact field updates without invoking a digest or a codec. They do not
compose the default-only codec adapters with enabled-checksum execution, and do
not implement placeholder checksum branches.

## Growable byte vectors

The installed standard models do not specify Vec `resize`, `truncate`, or
`as_mut_slice`. The extension instead calls checked application loops which push
zero bytes or pop trailing bytes, and obtains slices through the modeled range
indexing operation. These loops preserve the relevant byte contents and lengths;
their allocation strategy and execution cost differ from the release. Resource
exhaustion and physical allocation behavior are outside the modeled guarantee.

The explicitly named `onto_vec` functions specialize the release path by
inlining its resize/callback/truncate sequence and invoking the checked core
directly on the appended tail. They are not proofs of the generic Vec target
trait dispatch. On error they return before truncation, retaining the enlarged
vector and the core's partially modified tail. Success preserves the old prefix
and truncates the tail to the returned length. Any remaining capacity theorem
must be stated separately rather than hidden in an input-validity premise.

The checked mathematical capacity lemmas supply the release size estimate's
sufficiency and input-length decoding capacity. The runtime
`encode_decode_roundtrip` client composes the byte-vector encoder and decoder and
the proved uniqueness relation. The reverse round-trip direction is a theorem
about the mathematical relations, not a second runtime client. Exact leading-zero
counts are part of both uniqueness arguments.

## Copying and equality

Native builds retain the pre-existing derives. Under Creusot, the extension
uses exact field-copy Clone implementations for Alphabet and the three core error
enums. The error-enum implementation returns `*self`; this substitutes for the
derive's calls to field `clone`, because the installed `char::clone` model has no
exact-value postcondition. The application implementations' exact-copy
postconditions are checked. The error enums also use the stock DeepModel and
PartialEq derives, with the emitted equality bodies and refinements selected.
This does not establish exact Debug/Display output or add an original-release
Alphabet equality API.

The additional runtime wrappers do not request a blanket total-termination
check. Their functional and panic contracts must not be reported as proving that
arbitrary user callbacks terminate. The original core termination result and the
recursive logic lemmas' decreasing arguments remain separate evidence.

## Other boundaries and observations

The [model-boundary ledger](../verification/extensions/model-boundaries.md)
identifies precise missing contracts for owned/mutable strings, UTF-8 validation,
cryptographic dependency calls, and observable formatting. A successful model
probe is not a product API proof. No missing contract is filled by an assumed
application algorithm or a modification to the installed standard models.

Native comparisons use the pinned registry dependency and compare complete
buffers on success and error, including vector prefixes and enlarged error
states. Separate custom-target and stateful-`AsRef` witnesses explain why generic
semantic laws require premises. They are not new application defects and do not
establish universal source equivalence.
