# lexical-parse-integer 1.0.6

This workspace investigates the checksum-pinned crates.io release of
`lexical-parse-integer` 1.0.6. [source.lock.json](source.lock.json) identifies
the release archive and its files. The [specification](SPECIFICATION.md)
defines the intended parser behavior and an explicit coverage ledger; it is
not itself a proof of the Rust implementation.

The managed Aeneas profile is under [aeneas/profiles/default](aeneas/profiles/default).
Its [results](aeneas/profiles/default/results.md) describe the recorded proof
status and limitations. `scripts/setup.sh` prepares the pinned environment;
`scripts/verify.sh` runs the managed verification workflow. Native behavior
checks are separate from formal proofs.

The original complete parsing algorithm passes Charon extraction, but Aeneas
rejects a macro-expanded outer-loop break. The default, radix, and caller
profiles cover adapted block helpers and callers. The parser profile covers
complete and partial standard decimal u8 and i8 front-end adaptations, while
generic complete and partial front-end adaptations cover all integer widths
and radices 2 through 36 for arbitrary bytes, standard no-format syntax, and
no_multi_digit=true. The usize and isize front-end contracts assume a 64-bit
platform. Generic checked scalar adaptations also cover these widths and radices. Separate profiles cover sign handling and options, including an
adapted strict constructor. See the profile reports for precise premises and
results files for run status. Source checks and review support correspondence
of adaptations to the release, but do not formally prove Rust-to-Rust equivalence.
The original generic parser and pointer-based block callers remain unproved;
native differential checks are separate evidence.

Native checks reproduced two custom-format observations: [a single zero's
partial consumed length](verification/findings/LPI-001.md) and [an invalid byte
in a suffix format](verification/findings/LPI-002.md). The former matches an
existing upstream issue. The records include controls and reproduction commands.
