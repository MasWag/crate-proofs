# Extraction and proof scope

The target is the unchanged bs58 0.5.1 release at commit
`7d3c9282d2595612e5474df93dd0e017db9b684f`. Charon is the Aeneas-pinned
`08d7c9d50144bd84848212c24701253585e90d1f`; Aeneas is the unmodified
registered `be86ab0f1989d04944292b345b24c435be3ad10a`. The host uses
`nightly-2026-09-17`, target `x86_64-unknown-linux-gnu`, and Lean 4.35.0.

From the crate directory, the committed selected model is reproduced with:

```sh
charon cargo --preset=aeneas \
  --start-from 'crate::encode::EncodeBuilder::new' \
  --start-from 'crate::encode::EncodeBuilder::with_alphabet' \
  --start-from 'crate::decode::DecodeBuilder::new' \
  --start-from 'crate::decode::DecodeBuilder::with_alphabet' \
  --start-from 'crate::encode::max_encoded_len' \
  --dest-file proofs/Generated/bs58.llbc -- --lib --locked
aeneas -backend lean -emit-json -no-progress-bar \
  -dest proofs/Generated proofs/Generated/bs58.llbc
```

`charon` and `aeneas` above mean binaries built from those pinned, unmodified
commits. `max_encoded_len` is private and is included only for a possible helper
proof; it must not be mapped to an unrelated public API. The four public builder
methods are the selected claims. Their generated definitions contain no `axiom`
or `sorry` declarations. The model is for Cargo's default feature set, which
excludes `check` and `cb58`.

The full default library LLBC was also translated with the exact official
toolchain. `exact-full-translation.log` records the failed attempt. Aeneas
rejects nested-loop breaks in `encode_into`, `decode_into`, and
`decode_into_const`; it rejects the `u8` to `char` cast in `Alphabet::new`
(`Extract.ml:487`). The partial output was excluded from the proof package.
Consequently this report cannot establish general encoding, decoding, alphabet
construction, or round-trip correctness. `--consts values` for `BITCOIN` also
fails in exact Aeneas at `SymbolicToPure.translate_global`; see
`exact-const-translation.log`. No unsupported body is replaced by an axiom or
handwritten model.

`SPECIFICATIONS.md` states the intended full contracts and narrower families
for future verification. Only theorems actually built and selected in
`proofs.toml` should be described as proved.
