# Native findings for jsonptr 0.8.2

| Record | Observable failure | Upstream |
| --- | --- | --- |
| [JSONPTR-001](JSONPTR-001.md) | A partial-token prefix can produce a malformed Pointer. | [chanced/jsonptr#131](https://github.com/chanced/jsonptr/issues/131) |
| [JSONPTR-002](JSONPTR-002.md) | The maximum excluded start bound panics or selects the wrong slice. | Local draft |
| [JSONPTR-003](JSONPTR-003.md) | The diagnostic span for a final bare tilde extends past the input. | Local draft |
| [JSONPTR-004](JSONPTR-004.md) | The leading-zeros label panics for an all-zero index token. | Local draft |
| [JSONPTR-005](JSONPTR-005.md) | The invalid-character index label runs past the token or splits a character. | Local draft |
| [JSONPTR-006](JSONPTR-006.md) | `Diagnostic::url` names the wrong docs.rs page for three error types. | Local draft |
| [JSONPTR-007](JSONPTR-007.md) | `EncodingError::offset` documentation does not match tilde errors. | Local draft |
| [JSONPTR-008](JSONPTR-008.md) | Diagnostic helpers overflow on hand-built errors or mismatched subjects. | Local draft |

## Shared native evidence

The harness uses the untouched crates.io release at `../../.work/source` from
[its own Cargo manifest](../native/Cargo.toml). It enables the `resolve` and
`assign` features and no other jsonptr features. These two features add no
dependencies, so the lockfile is unchanged from the earlier three-test
harness. The [release source lock](../../source.lock.json)
has SHA-256 `a477f590f8c1bf6e8819af7cc49c2349d2f2d649de067b9b164b10a184dbb880`.
The release archive has SHA-256
`72c22d99362c7aac7d77efab6b49c2181674b165d7e6e7c755b3432ded64bf51`.

| Harness file | SHA-256 |
| --- | --- |
| [`Cargo.toml`](../native/Cargo.toml) | `2edeccafed967c0ef243bc76a395c786835997dd4e253510334e0cbc8896f4ca` |
| [`Cargo.lock`](../native/Cargo.lock) | `d758fdc16d7bdf22ca314fbf2ac817c46195e880ec6f049b089d18653b56cd59` |
| [`src/main.rs`](../native/src/main.rs) | `52ee84f9a7b83bb05573d75374d3f6258a0c2f7fc0effbd93331da1755ecd81d` |

Run from `/private/tmp` to avoid inheriting the repository's root Cargo
configuration. Set `target` to the crate version's absolute directory.

```sh
target="$(pwd)"  # run this line from the version root, then:
cd /private/tmp
cargo +1.91.0 test --locked --offline --manifest-path "$target/verification/native/Cargo.toml" --target-dir "$target/.work/native" -- --nocapture
cargo +1.91.0 test --release --locked --offline --manifest-path "$target/verification/native/Cargo.toml" --target-dir "$target/.work/native" -- --nocapture
```

The November 28, 2026 runs used Rust 1.91.0
(`f8297e351a40c1439a467bbbb6879088047f50b3`) on macOS 26.6.2 (25G83), host and target
`aarch64-apple-darwin`. Default Cargo debug checks integer overflow, and
default release wraps it. The runs used a draft copy of this harness with
the same three files listed above. Its `../../.work/source` resolved to this
version's release directory, and it used a separate target directory. Both
commands exited 0 with eight tests passed. The tests assert the observed
defects, so passing means the counterexamples were reproduced. An
independent reviewer reran the draft copy on 2026-11-28 in debug and
release, with eight tests passed in each, and also reran the issue snippets
and the miette probe. On 2026-11-28 the installed harness was rerun with
the commands above; debug and release each exited 0 with eight tests passed.
The local-only logs `.work/native-installed.log` and
`.work/native-installed-release.log` have SHA-256
`d403f48c07171d97b5e91bbcb25b65513eb32e5e68247164d246562210ca99f0` and
`213ebff6a70d08018e29241b37191cf6290562ce1cad17375c7d1cb2570e44f5`.

The full logs are local-only under the version's ignored `.work/` directory.

| Log | SHA-256 |
| --- | --- |
| `.work/native-debug.log` | `ca041c3d1a0555fca5a43401f295295fa63cad93774decc844e67611f9569b3d` |
| `.work/native-release.log` | `eb6393b1b170bd1300a41d069f1ad1bce7f9e9dad3428b6f9e9d019595cfbed8` |

The November 27, 2026 three-test runs had logs
`b473bc4d7f9569adc721b14387bbfa09d837e2d30f965bd8150be3a92667d164` (debug)
and `bae1e704db9385dba78c654712d59e9a021079a8a64d7b84081cf125aa8e36b1`
(release) and harness source
`0e58011b351d29fd14ae756f75addb1fe7e8ca9f758fd02242bc8a41e8d64c58`.

### miette rendering probe

JSONPTR-004 and JSONPTR-005 also cite a separate scratch program. It is not
part of the harness. It depends on the same release path with
`default-features = false, features = ["miette"]` and on `miette = "7.4.0"`.
Its lockfile was generated offline from the local registry cache and
selected miette 7.4.0. For each input given as an argument, it calls
`Index::try_from(input).diagnose(input)` and prints
`miette::Report::new(report)` with `{:?}`. It was run with
`NO_COLOR=1 cargo +1.91.0 run [--release] --offline --locked` from
`/private/tmp`.

For `00` and `000`, both profiles printed the message and panicked at
`index.rs:376` with exit 101. `01`, `1abc`, `aé1` and `bar` exited 0.

| Probe file | SHA-256 |
| --- | --- |
| `src/main.rs` | `e78cf786b5b9a172f3d4918ac3e14c87e6759523246d1b7cef694373b826e2a8` |
| `Cargo.lock` | `d24b3860f3d6292ce9f6f9fa2319289214a30b4839d4f67cbde58087468656dc` |
| `.work/miette.log` | `01ac89a9b923d5ab763d8d124ab934041c7ee42d44584eb7e81e88996230ea13` |

These files are local-only and are not checked in.

## Upstream issue drafts

The issue search found an existing matching report for JSONPTR-001. Its local
draft is a version-specific follow-up. The searches found no matching issue
for JSONPTR-002 through JSONPTR-008. Closed issue
[chanced/jsonptr#128](https://github.com/chanced/jsonptr/issues/128) concerns
`"~~0"` acceptance, which is related to JSONPTR-007's field but is not the
same report. No issue or comment was submitted.

The [upstream default-branch tree](https://api.github.com/repos/chanced/jsonptr/git/trees/41a813bd4e7e89a0251bf2fc559c7159933a1066?recursive=1)
had no issue templates, issue-form configuration, or contribution file.
On 2026-11-28 the default branch was still at that commit. By source
inspection, the code and documentation behind JSONPTR-004 through JSONPTR-008
are unchanged there. The [upstream README](https://github.com/chanced/jsonptr#contributing)
invites tickets or pull requests. The local new-issue drafts use the
[github-issues bug-report template](https://github.com/github/awesome-copilot/blob/main/skills/github-issues/references/templates.md).

Each draft's Rust snippet was compiled verbatim with `rustc +1.91.0` against
the debug and release jsonptr libraries built by the harness. Debug snippets
used overflow checks, and release snippets used `-C opt-level=3` without them. On November 27, 2026, the JSONPTR-001
to JSONPTR-003 snippets gave six executions. Each exited 101 at the
documented assertion or overflow. Their local-only log
`.work/native/issue-snippets.log` has SHA-256
`af7ada3817c2e4f1059a6ac84f9b372b4424e360c13bc1ceaa17fa37e19bfa53`.
On November 28, 2026, the JSONPTR-004 to JSONPTR-008 snippets gave ten
executions. Each exited 101 at the documented panic or assertion, including
the overflow panic for JSONPTR-008 in debug. Their local-only log
`.work/native/issue-snippets-004-008.log` has SHA-256
`262d5d6f1fb6ea6aa473d5d6f1c947fb3cdc8d27be066688998e0951590eff20`.
