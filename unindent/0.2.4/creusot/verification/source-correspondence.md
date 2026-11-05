# Source correspondence

The proof subject is the annotated implementation in `../src`, an independent
`unindent` 0.2.4 Cargo workspace. It is an executable adaptation of the registry
release, not the unchanged registry implementation. The release archive and file
inventory are pinned in `../../source.lock.json`; the authoritative restored file
is `../../.work/source/src/unindent.rs` (SHA-256
`67b3a28101a04bdbda340a9b2747190993f7d88746bc14f0220769efeea189a4`).
The existing Aeneas subjects and immutable release source were not changed.

`patches/creusot-source.patch` is the complete textual diff from that release
algorithm file to the adapted `src/lib.rs`, including contracts, ghost state,
module declarations and native tests. Additional specification and proof modules
are fingerprinted separately by the fresh runner.

## Resolved annotation dependency

The manifest requires `creusot-std = "=0.13.0"` without a local path patch.
The offline locked Cargo metadata resolves both `creusot-std` 0.13.0 and
`creusot-std-proc` 0.13.0 from the crates.io registry, under the isolated
environment's `cargo/registry/src/index.crates.io-1949cf8c6b5b557f/` directory.
They are not taken from the installed verifier source checkout or the separate
`~/creusot` development tree. The final runner fingerprints the resolved sources,
lockfile and active Cargo configuration.

An inherited `/home/lab8/mwaga/.cargo/config.toml` declares a path patch for
`creusot-std` 0.15.0-dev. Cargo reports it as unused: it does not satisfy this
workspace's exact 0.13.0 requirement. That warning and the corresponding unused
patch lock record are not evidence that the development model is selected.
The workspace's earlier redundant local path-patch declaration was removed;
locked metadata records the actual registry identities above.

## Executable changes and function map

| Release operation | Adapted operation | Reason and behavior to preserve |
| --- | --- | --- |
| `unindent_bytes(s)` delegates with `false` | Same public delegation | Preserve arbitrary byte inputs, including invalid UTF-8. |
| `do_unindent_bytes`: `lines().skip(1).filter_map(count_spaces).min().unwrap_or(0)` | `common_margin` scans LF endpoints with `line_end_index` and leading whitespace with `leading_end_index` | Frozen Creusot lacks `IteratorSpec` for the callback-pointer `slice::Split`. The checked minimum is attained by an eligible later line, lower-bounds every eligible indentation, and defaults to zero only when there is no eligible candidate. |
| `count_spaces` returns the first non-SPACE/non-TAB offset, excluding whitespace-only lines | `leading_end_index` returns the first such byte or the field endpoint | Preserve one-byte tab counting and the distinction between an eligible zero indentation and an absent candidate. |
| `BytesExt::lines` removes one initial CR when followed by LF, then splits on LF | Byte scan identifies initial CRLF and tracks the source index immediately after the most recent LF | Preserve initial CR removal, all other CR bytes, and empty leading/interior/trailing fields. |
| Enumerated fields are trimmed and LF bytes reconstructed between retained fields | Scan original bytes once, retaining each source LF except an optionally suppressed initial LF, and retaining later-field bytes exactly when their offset reaches the common margin | Reconstructed release separators correspond to original LF bytes. The source selection preserves order, never inserts or changes a byte, and deletes no bytes at or above 128. The same-line first field is not trimmed. |
| Private `do_unindent(s,p)` converts bytes, calls the flagged byte core, then `String::from_utf8(...).unwrap()` | Same conversion/call/unwrap structure with checked preservation lemmas | Preserve both values of the private flag and discharge successful UTF-8 conversion through ASCII-erasure preservation. Standard-library boundaries are listed in `assumptions.md`. |
| Concrete `Unindent` implementations for `[u8]`, `str`, `String` | Same delegation with explicit body contracts | Preserve returned contents and delegation. |
| Generic `Unindent for &T` | Original delegation retained under `cfg(not(creusot))` | Preserve native downstream behavior. Arbitrary user implementations have no universal success or output contract; this implementation is excluded from selected formal targets. |

The earlier linewise explicit-index Aeneas adaptation is not the final Creusot
byte implementation. Its existing patch must not be used as the source map for
this track. The present output scan is the additional adaptation described above.

The original source was probed with frozen Creusot 0.13. Extraction failed at
`.lines().skip(1)` because `std::slice::Split<u8, fn(&u8) -> bool>` does not implement
`IteratorSpec`. The actual diagnostic and probe source are retained in ignored
`.work/original-extraction.log` and `.work/original-probe.rs`. This is a tool/model
boundary, not a reported defect in the crate.

## Specification and equivalence boundary

The adapted core's contract is `spec::source_unindented`: an attained source-line
minimum and a complete, strictly ordered trace of exactly the retained source
positions, with exact output byte equality. It is a declarative source-position
specification, independent of the operational scan. The checked core also returns
at most the input byte length and has explicit termination obligations. The
String contract describes the same byte relation and successful UTF-8 conversion.

The independent specification also defines the LF-field decomposition model
`spec::unindented` (`U_p`). A machine-checked equivalence between the source-position
and decomposition formulations remains an open obligation. Their mathematical
correspondence has independent specification review, but that review is not a
checked equivalence theorem.

No machine-checked all-input equivalence between the adapted executable source
and the registry implementation has been established. Matching package names,
versions, source review and finite comparisons do not establish such a theorem.
The formal scope therefore describes the adapted source and its exact
source-position contracts; it does not silently extend that scope to unchanged
release bodies or the unproved decomposition bridge.

## Native correspondence checks

Run separately from formal proof, from this workspace:

```sh
source scripts/env.sh
cargo test --offline --locked -- --nocapture
```

`tests/differential.rs` calls the actual restored release module and compares:

- 300,617 arbitrary-byte inputs: all sequences of length zero through six over
  `[0, TAB, LF, CR, SPACE, A, 128, 255]`, plus deterministic generated byte inputs
  of every length zero through 1023. The public byte function is checked on all
  cases; the concrete byte extension method is also checked on the exhaustive set.
- 299,593 Unicode inputs: all sequences of length zero through six over
  `[NUL, TAB, LF, CR, SPACE, A, é, 🦀]`. The public string function and concrete
  `str` and `String` extension methods are compared with the release.

The `flag_tests` native unit test compares the private String and byte cores
against the release's private flagged String wrapper for all sequences of length
zero through five over the same Unicode alphabet, for both flag values: 74,898
input/flag pairs. This flagged comparison covers valid UTF-8 inputs; it is not a
separate arbitrary-byte flagged differential test.

Exploratory execution passed these checks in `.work/native-full-flagged.log`.
The final run's archived native log and source fingerprints own the fresh outcome.
These tests establish observed agreement on their finite inputs, separately from
formal proof and separately from all-input release equivalence.
