# leb128fmt 0.1.0

Use the repository Aeneas Lean verification skill, the managed default profile,
and its pinned native Rust, extraction Rust and Lean environments. Start with
`bash scripts/setup.sh --offline` from this directory when local caches exist.
Run `bash scripts/verify.sh --offline` for acceptance. The runner requires
Python 3.11 and the selected models target `aarch64-apple-darwin`.

Keep the registry archive and restored release bytes immutable. Keep Aeneas and
Charon unpatched. Compare extracted bodies to the maintained generated files and
audit all checked theorems. Distinguish public API theorems, extraction-only
probes and native behavior. Use the default profile's specification to preserve
the exact input domains and error behavior.

The specification owner defines the independent arithmetic meaning and API
inventory. The implementation owner develops extraction, proofs and runnable
evidence. The primary reviews source correspondence, contracts, commands,
coverage and audit results.
