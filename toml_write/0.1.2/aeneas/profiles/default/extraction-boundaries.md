# Release body extraction boundaries

The probes used Aeneas `be86ab0f1989d04944292b345b24c435be3ad10a` and its pinned Charon `08d7c9d50144bd84848212c24701253585e90d1f` from unpatched upstream trees. The release source stayed at the checksum in `source.lock.json`. Upstream Aeneas HEAD observed on 2026-11-25 was `fb44cb400eb6bfe7dce97422ebe8fa748b7e4f9b`, with Charon `695be3d6292e988eedd8afcb7a709146a0ff4f01` and Lean 4.36.0. This newer compiler was not used for the accepted proof. Its bootstrap required newer GNU Make and an additional OCaml dependency, `ppx_deriving_hash`.

The original writer probe ran these tool arguments from the version root, using a fresh output directory and the extraction Rust lock.

```sh
charon cargo --preset=aeneas \
  --start-from 'crate::string::write_toml_value' \
  --start-from 'crate::string::_::calculate' \
  --dest-file "$output/toml_write.llbc" -- --lib --locked
aeneas -backend lean -dest "$output" "$output/toml_write.llbc"
```

Aeneas reported early returns inside loops at `string.rs:193–298` and dropped the generic string writer body. It also diagnosed mutually recursive trait declarations for `TomlWrite`, `WriteTomlKey`, and `WriteTomlValue`. Partial generated output from this probe was rejected. A local refactoring of the loop control flow would address the first issue but leave the Rust formatting, trait dictionary, and sink effects to model. No refactored writer is used as release evidence.

To reproduce the default-selector diagnosis, add `--start-from 'crate::string::_::as_default'` and `--include 'crate::string::_::as_default'` to the Charon invocation derived by [extract-split.py](../../../scripts/extract-split.py). This selected both original default bodies. The option combinators introduced callback implementations whose borrowed captures triggered “Can't end abstraction … as it is set as non-endable” at `string.rs:17–20,124–126`. The partial extraction was rejected.

The maintained [default-selection patch](patches/default-selection.patch) replaces the two closure chains with ordered early returns and preserves their fallback calls and newline condition. The derived copy renames the encoding enum to `DefaultEncoding` and keeps `Encoding` as a type alias so that the two generated Lean modules can coexist without a discriminant-instance name collision. The enum representation and variants are identical. [The extraction check](../../../scripts/extract-default-selection.py) stages the patch in a separate directory, regenerates the two bodies with the unchanged pinned tools, and compares the generated Lean byte-for-byte. The check records the release Rust, adapted Rust, and patch SHA-256 digests.

[The Lean proofs](proofs/DefaultSelectionProofs.lean) check the generated adapted bodies for arbitrary raw builders and compose them with the original constructors through field-preserving adapters. The string composition requires both maximum quote runs to fit in the release counters. Separate Lean equations relate the modeled lazy option chains to the ordered selection specification. Applying those equations to the original Rust callbacks relies on source review of the patch. The native comparison includes both Rust sources and compares descriptor fields over all 32 key and 524,288 string metric states with one fixed decoded string.

Directly including `core::str::_::as_bytes`, `core::str::_::is_empty`, and `core::str::_::len` for the metric bodies exposed an unsupported transmute from `&str` to `&[u8]`. The maintained split extraction gives the two standard calls definitions over Aeneas's existing `Str = Slice U8` representation. The two definitions are version-local and preserve the observations used by the selected Rust code. The generated application definitions and their source spans remain untouched.

## Fixed writer tokens

A separate probe selected `crate::write::TomlWrite::open_table_header` as the Charon root with the `--exclude` selectors `crate::write::TomlWrite::key` and `crate::write::TomlWrite::value`. The generated declarations still contained the recursive trait dictionary fields, and Aeneas diagnosed that the generated types would fail Lean checking.

The pinned backend also represents `core::fmt::Arguments` as `Unit`. Its `Arguments.from_str` operation discards the input string. Consequently, generated fixed-token methods dispatch `write_fmt` with the same argument for distinct tokens. The emitted token cannot be recovered from the stock model. Switching the Rust macros to direct `write_str` calls can change behavior because a sink may override `write_fmt`. Exact byte or effect contracts for these methods require a formatting model that retains the literals and preserves the original dispatch.

The fixed-token probe retains local logs in `.work/writer-next`. Its Aeneas log has SHA-256 `7c06c065c15438a7a8dfff93c83c8e93439dfb10ab45d925acb01b8efab5eadd`. The pinned backend file implementing these observations is `backends/lean/Aeneas/Std/Core/Fmt.lean` (SHA-256 `3035c0a5245602b429ab819bc9ee0db398a6f058c59f9b6302e0c45ea063f3c8`). The observed newer upstream revision retains the same unit representation and literal-discarding operation in that file (SHA-256 `a802741356d8f7814a7d0655910fa287755000909144183d35657d1ce9eecf2c`).
