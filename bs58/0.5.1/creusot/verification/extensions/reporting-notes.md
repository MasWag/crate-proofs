# Standard recorder API-binding limitation

This is a reporting-tool observation, not an unverified bs58 body or a bs58
runtime defect. The unmodified cargo-proofs 0.4.1 run
`ec72449d-897f-42a7-8b97-d04dead9eab0` verifies the full generated workspace but
binds only 21 fork callables to its recorded API entries. Generic builder methods
are absent from that binding list; their bodies remain in the complete accepted
canonical and native proof inventories.

The inspected installed package source is
`cargo-proofs-0.4.1/src/scan.rs`. Its `Item::Impl` inherent-method branch rejects
the self path when `segments(&owner.path)` returns an error. `segments` rejects
every path segment with generic arguments, so a legal inherent impl such as
`impl<'a, I: AsRef<[u8]>> EncodeBuilder<'a, I>` is skipped. A generic free function
does not take that branch and remains discoverable. A previous, separately
reviewed [Aeneas reporting patch](../../../aeneas/profiles/default/patches/cargo-proofs-preparation.patch)
contains the corresponding generic-owner discovery correction.

The continuation retained the unmodified installed reporting CLI. No missing
contracts were inserted into SARIF and no successful proof result was fabricated.
The submitted SARIF bytes match their recorded SHA-256. Its source-bound
21-entry subset is published alongside the complete
[functional proof inventory](evidence/goal-inventory.json) and the
[native declaration/root audit](../../extensions/publication/native-goal-audit.json).
The latter reconstructs every retained native Coma target and matches all 242
original roots to positive proof trees, including omitted builder methods.

Generated derive methods and trait refinements likewise should be read from the
complete inventory rather than inferred from source-only API-binding counts.
Recorded API names identify the verification fork; Rustdoc signatures and safety
classifications were not independently imported for these entries.
