# bs58 0.5.1 verification target

- Source is the unchanged crates.io bs58 0.5.1 archive, restored into `.work/source` from `source.lock.json`.
- The `default` Aeneas profile selects five original Rust function bodies with default features; four public builder methods have Lean contracts. `max_encoded_len` is extracted but not claimed as proved.
- Keep Aeneas and Charon at the exact unmodified commits in `toolchain.lock.json`. Do not patch or replace application bodies, generated Lean, or source files to obtain a proof.
- Native tests and checksum findings are separate from formal verification. Do not claim the general codec, alphabet constructor, checksum implementations, or whole crate are verified.
- Specification design, proof implementation, and independent review remain explicit. Run `scripts/setup.sh`, then `scripts/verify.sh`; preserve failed runs and report current evidence precisely.
