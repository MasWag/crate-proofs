# bs58 0.5.1 proof target

This independent Cargo workspace compiles the unchanged crates.io release restored from `source.lock.json` into `.work/source`. The selected Aeneas profile uses the release's default features (`std` and `alloc`, without checksum features). It extracts five original function bodies and maps four public builder contracts to Lean theorems. The fifth, private `max_encoded_len`, is extracted without a correctness claim.

The mapped methods are `EncodeBuilder::new`, `EncodeBuilder::with_alphabet`, `DecodeBuilder::new`, and `DecodeBuilder::with_alphabet`. Their contracts specify the stored input and alphabet and checksum mode. No codec, round-trip, alphabet-construction, buffer, or checksum correctness claim follows from them.

Run from this directory:

```sh
bash scripts/setup.sh
bash scripts/verify.sh
bash scripts/verify.sh --offline
```

The managed runner checks source and tool identities, native tests, fresh Aeneas regeneration, Lake build, theorem mappings, and transitive axioms. The `evidence/reproduce-findings` package independently asserts three checksum-related findings with `check` and `cb58` enabled. `aeneas/profiles/default/results.md` records the current managed result; `proofs.toml` in that profile is the reader-facing proofs.rs report.
