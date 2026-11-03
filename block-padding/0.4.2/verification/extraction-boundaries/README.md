# Generic API extraction probes

These are diagnostic attempts, not proof runs. They used the pins in `aeneas/profiles/default/toolchain.lock.json` on `aarch64-apple-darwin`. Aeneas and Charon were unpatched. The subject was the maintained verification harness, which adapts the release's two iterator checks to explicit loops; the concrete probe additionally appended the two wrappers below. No equivalence proof to the release is implied. The original `.work` logs and generated output named below are local, ignored artifacts; their digests identify them but do not make them downloadable.

```rust
pub fn probe_pad_16(b: &mut Array<u8, hybrid_array::typenum::U16>, pos: usize) { Pkcs7::pad(b, pos); }
pub fn probe_unpad_16(b: &Array<u8, hybrid_array::typenum::U16>) -> Result<&[u8], Error> { <Pkcs7 as Padding>::unpad(b) }
```

The probe harness was copied from `verification/harness`, with its documentation `include_str!` path changed to `../../source/README.md` for its location under `.work/concrete-harness`, and the wrappers appended. Its source SHA-256 was `697a1005de6e3b3283e22dc66d12cd16b7ea846593bd308b25bc5bdba807bdd9`; the maintained source at the time was `7f292669f19c2d04cbeb84784cd70461c48cad0c2d346d4b15a437eaeec659d3`. The three copied JSON files retain the exact selection settings. Reproduction requires restoring the pinned source and tools and recreating the temporary harness and fresh output directories. From the repository root, the extraction helper was invoked in an environment with `BASH_ENV`, `ENV`, `CPPFLAGS`, and `LDFLAGS` unset, `AENEAS_EXTRACT_RUST=nightly-2026-09-17`, `RUSTUP_TOOLCHAIN=1.91.1`, and the pinned Aeneas and Charon binaries and rustup proxies on `PATH`:

```text
python3.11 scripts/aeneas-extract.py block-padding/0.4.2/verification/harness --config block-padding/0.4.2/verification/extraction-boundaries/highlevel-config.json --output block-padding/0.4.2/.work/probe-highlevel
python3.11 scripts/aeneas-extract.py block-padding/0.4.2/.work/concrete-harness --config block-padding/0.4.2/verification/extraction-boundaries/concrete-config.json --output block-padding/0.4.2/.work/probe-concrete2
python3.11 scripts/aeneas-extract.py block-padding/0.4.2/.work/concrete-harness --config block-padding/0.4.2/verification/extraction-boundaries/concrete-pruned-config.json --output block-padding/0.4.2/.work/probe-concrete-pruned
```

In all three, Charon succeeded, then Aeneas exited 2 reporting unsupported mixed mutually recursive declarations, including `hybrid_array::Array`. The third attempt enabled `remove_unused_clauses` and had the same boundary. Charon logs also record an unsuccessful Miri sysroot setup and fallback to rustc's default sysroot for these sandbox probes. A managed final extraction needs its own recorded sysroot conditions.

A separate direct monomorphized extraction of both U16 wrappers used the commands saved in `.work/probe-concrete-mono/commands.json`: Charon exited 0. Its first Aeneas command used unsupported `-rooted-declarations` and `-filter-trait-methods` flags and exited 2; that invalid invocation is not evidence of a translation blocker. A retry using the supported command in `supported-command.json` exited 1 with `expand_symbolic_value_no_branching: unexpected type: ... TSlice` while translating the private PKCS unpad helper. Copies of these command vectors are retained as `concrete-mono-commands.json` and `concrete-mono-supported-command.json`; their absolute paths are the original machine paths and must be adjusted when replaying elsewhere. The commands ran with the concrete harness as working directory, except the supported Aeneas retry, which used repository root and absolute paths.

The pad-only monomorphized commands, also retained as `concrete-pad-mono-commands.json` with original absolute paths, both exited 0, but generated Lean contains an application axiom for `hybrid_array::Array::as_mut_slice` and monomorphized standard-library axioms. It is therefore not acceptable as an axiom-free extracted proof subject. These attempts do not establish that a different extraction or checked representation bridge is impossible.

## Local artifact SHA-256

Paths below are relative to `block-padding/0.4.2`; `.work` artifacts may need to be regenerated.

```text
a606fed42cb44683c62c89804a863fcfe0925bb109bbffb51bf7aea524290477  .work/probe-highlevel/charon.log
ea835aca186031a508eff3f36002972dce44d4430f7c06602e66910f87e36dfe  .work/probe-highlevel/aeneas.log
72db7c7ce271f3b193b90e711f0fad917d02527fa595c8792f2ac5cf288a817a  .work/probe-concrete2/charon.log
5f9d289fce28926232d367192e2186164ad6b7e68cacd192c4fce87fa3d2453f  .work/probe-concrete2/aeneas.log
f825da35322ea741bc282ee64fa05578d8bedae2dd6f6b820941ec74e358de88  .work/probe-concrete-pruned/charon.log
11dc1ef138b1799e069300b2935b2bc973ee919afa0732e3a7b6a3dcb61b481d  .work/probe-concrete-pruned/aeneas.log
ba4c6595d1641926025f28e61dc3a003240f250470a630f8329de524bd620231  .work/probe-concrete-mono/commands.json
0422a09a4215ec8ff04147095d404faccf4f0516870b85f440968ceb92b6efc1  .work/probe-concrete-mono/supported-command.json
5a49f398f2474998e6b957e0dd62f66b2b099fa72e249cca29ff65c47552252c  .work/probe-concrete-mono/aeneas-supported.log
4efc149fd8e4767f491b8b52a83acfdcc2eb97ff67f417b990be4759c07a2b97  .work/probe-concrete-pad-mono/commands.json
9ecb15cf8f41746762d875fa473b406c829db19bed456cd3f0352e5bf2ea5a24  .work/probe-concrete-pad-mono/charon.log
eb2a39f93b3d1f70803ed0725c93e822c6db0c391da601a68e4410bed0ddc1e9  .work/probe-concrete-pad-mono/aeneas.log
38e41d0c3f64a7c5bf5339203d8863b58f3435b9ad01a055ca608712d8e2c69e  .work/probe-concrete-pad-mono/BlockPaddingVerificationApi.lean
6f83d95e80d314c57ef14da55a8bc7e4ffd75fc1af13b90371f718ed0b04cdc7  verification/extraction-boundaries/concrete-config.json
a1797062ca95a8cf570378463d8350a4274181b9ce810b02f62e1c0e45206ec9  verification/extraction-boundaries/concrete-pruned-config.json
d99ddc31b4257c608a18d663808ad597bf368fcd7edac0797329d99ad6d3b913  verification/extraction-boundaries/highlevel-config.json
```
