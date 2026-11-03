# Results and coverage ledger

The intended contracts are defined in [SPECIFICATION.md](SPECIFICATION.md). The twelve listed raw contracts passed the managed default-profile run and were independently reviewed. The [local run result](.work/runs/default-5vsmgxk0/result.json) and [named theorem and transitive axiom audit](.work/runs/default-5vsmgxk0/audit/result.json) passed; these ignored artifacts are local to this workspace. Their theorem mappings and premises are in [proofs.toml](aeneas/profiles/default/proofs.toml). The audit checks the named Lean theorems and transitive axioms; it is not a formal equivalence proof between the adapted source and release. Native tests are recorded separately below.

## Raw algorithms

| Algorithm | `raw_pad` | `raw_unpad` |
|---|---|---|
| ZeroPadding | `zero_pad_total`; `pos ≤ len` | `zero_unpad_total`; all slices |
| Pkcs7 | `pkcs_pad_total`; `pos < len ≤ 255` | `pkcs_unpad_total`; `0 < len ≤ 255` |
| Iso10126 | `iso10126_pad_total`; `pos < len ≤ 255` | `iso10126_unpad_total`; `0 < len ≤ 255` |
| AnsiX923 | `ansi_pad_total`; `pos < len ≤ 255` | `ansi_unpad_total`; `0 < len ≤ 255` |
| Iso7816 | `iso7816_pad_total`; `pos < len` | `iso_unpad_total`; all slices |
| NoPadding | `no_pad`; `pos ≤ len` | `no_unpad`; all slices |

The compiled padding contracts describe every output byte on the stated domains. The compiled unpadding contracts describe the returned prefix and acceptance and error cases on the stated domains. The contracts are not panic proofs outside those domains. Any valid-domain proof must be reported with its exact premises; it cannot establish the documented all-input malformed-padding behavior by itself.

## Other boundaries

The statuses below describe the general Aeneas scope. The separate [Kani workspace](kani/RESULTS.md) additionally checks concrete U16 instances on bounded inputs; those results do not close the general Aeneas gaps.

| Entry | Intended scope | Status |
|---|---|---|
| Private `Pkcs7::unpad` | Both strict and non-strict modes and their raw callers | Named helper proofs passed the managed audit. |
| Typed `Padding::pad` and `Padding::unpad` | Each of the six implementations and the array representation bridge | Unproved; generic extraction blocked in the recorded probe. A concrete U16 retry also encountered translation/model boundaries. |
| `pad_detached` | Four defaults and ZeroPadding/NoPadding overrides; all variants, input prefix and tail | Unproved; generic extraction blocked in the recorded probe. |
| `unpad_blocks` | Four defaults and ZeroPadding/NoPadding overrides; empty list, last block, flattened output | Unproved; generic extraction blocked in the recorded probe. |
| `PaddedData::unwrap` | Success and both panic arms | Unproved. |
| `Error`, marker types, `PaddedData`, `array` re-export | Formatting, derives, variants and dependency boundary | Unproved. |
| Roundtrips | Four reversible schemes and the distinct ZeroPadding and NoPadding behavior | Separate composition laws unproved. |

The [extraction boundary record](verification/extraction-boundaries/README.md) describes the failed generic and concrete probes. These results establish limitations of those attempts, not impossibility of verification. Generic zero-sized arrays and external `hybrid-array` behavior require explicit analysis; no all-size or downstream-implementation claim is made here.

## Native observations

Against the pinned release source, native debug and release tests observed that `Pkcs7::raw_unpad`, `Iso10126::raw_unpad`, and `AnsiX923::raw_unpad` panic for an empty slice. The trait documentation says malformed padding returns an error, and these schemes require a final count byte. `tests/empty_unpad.rs` also checks the distinct empty-input behavior of the other three implementations. `tests/representative_failure.rs` contains an ignored assertion expecting `Err`; an explicit run fails on the original source. These tests demonstrate particular inputs and do not establish formal correctness or a formal panic theorem.

The managed run on `aarch64-apple-darwin` checked the derived source and exact regenerated model and recorded identical before/after input fingerprints. Its Charon log records a failed Miri sysroot setup followed by fallback to rustc’s default sysroot. From this version directory, the native commands were `cargo test --locked` and `cargo test --locked --release`; their local [debug](.work/runs/default-5vsmgxk0/native-0.log) and [release](.work/runs/default-5vsmgxk0/native-1.log) logs passed. These native observations are separate from formal verification.
