# jsonptr 0.8.2 Aeneas verification

- Follow the repository Aeneas and Lean verification skill. Use this version’s managed profile and keep tool checkouts unpatched.
- Use the checksum-pinned crates.io source in `.work/source`. Keep the Cargo workspace independent. The extraction target is `aarch64-apple-darwin` with no default features. Native tests use both default features and all features.
- Check the pointer byte grammar, including exact first-error offsets at the release caller’s zero offset, and the model of index resolution. Track public parse, token encoding and decoding, index parsing, and JSON/TOML resolution separately in the coverage ledger.
- Maintain independent specifications, implementation proofs, and primary review. An extracted or successfully tested API does not count as proved.
- Run `bash scripts/setup.sh` and `bash scripts/verify.sh --offline` with Python 3.11 or newer and the pinned tool cache. Keep investigation runs and restored sources ignored.
