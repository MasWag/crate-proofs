# Native behavior findings

> **Native compiler correction:** The original native runs used rustc 1.99.1. Fresh runs explicitly pinned to rustc 1.94.1 reproduce all reported native results; see [the recheck record](../../publication/native-recheck.json). Original evidence remains unchanged.

- [LC-001](LC-001.md): single-zero consumption undercounts; [issue-ready draft](LC-001-issue.md). This is the known upstream [#225](https://github.com/Alexhuszagh/rust-lexical/issues/225) symptom.
- [LC-002](LC-002.md): a configured suffix can advance past an unrelated byte; [issue-ready draft](LC-002-issue.md).

Both observations use the actual lexical-core 1.0.6 public APIs and unchanged crates.io source. They originate in lexical-parse-integer 1.0.6 and are retained under this facade version because they are observable through it. These are two causes, with four regression assertions, not four bugs. No issue was filed and no fix was applied.

The issue drafts follow the upstream bug template read on 2026-11-10, `.github/ISSUE_TEMPLATE/bug_report.md`, blob `4e65de2fae75debde4c6a0f02c787123047a536d`. The GitHub Issues skill and template reference were read from `github/awesome-copilot` main; the official report skill was read from the local proofs-rs checkout at revision `2446bcad7d492be2d2036629e5dc94d186a23213` in cache `2bbcd162cdc644dc88e6c46bcba0e1011a6f80b5cff9c0e8b2cb72d7bca7b938`. These remain local drafts. Independent Astra review checked raw source, logs, hashes, archive member bytes, causes and issue #225 on 2026-11-10; the reviewer did not rerun native tests. Primary also inspected raw logs.

The current upstream template directory was inspected and a root `CONTRIBUTING.md` read returned 404. A repository issue search for `suffix` found no exact match for LC-002; this is not an exhaustive novelty check. Upstream fixes were not checked.

See the [native harness](../behavior/README.md) and [evidence manifest](../behavior/evidence.json) for exact inputs, commands, source checks and local-only log digests. Native regression tests do not establish formal correctness.

## 2026-11-10 native compiler provenance correction

The original native run's target `.rustc_info.json` identifies Homebrew rustc 1.99.1, despite the command selecting Cargo through `rustup run 1.94.1`. The earlier Rust 1.94.1 attribution in the retained native evidence describes the intended toolchain, not the compiler actually used. Original logs, manifests and hashes are preserved unchanged.

A fresh recheck explicitly selected the absolute Cargo and rustc 1.94.1 binaries and prepended that toolchain's `bin` directory to `PATH`. Both fresh targets' `.rustc_info.json` confirm `rustc 1.94.1 (e408947bf 2026-03-25)`. Controls passed, the four ignored expected-correct regression assertions and both issue snippets reproduced their documented failures, and all 4,608 compact comparison cases passed. The public issue snippets' Rust 1.94.1 prerequisite is supported by this fresh run. No Rust proof input, generated Lean, specification or formal theorem changed.

See [the append-only native recheck record](../../publication/native-recheck.json) for exact commands, compiler metadata, source/log digests and local-only evidence availability.
