# utf-8 0.7.6 publication adapter

The publication CLI uses proofs-rs commit `2446bcad7d492be2d2036629e5dc94d186a23213`, the existing preparation patch, and the explicitly locked publication patch. Aeneas, Charon, generated models and theorems are unchanged. This adapter is scoped to this crate's seven mappings; its source scanner is not a general Rust macro or specialized-impl resolver.

The patch accepts typed findings, creates them with new reports, preserves independent findings history on revisions, and resolves optional finding API links. It recognizes this release's generic decoder constructors and built-in derived Clone methods. The Clone mappings use canonical trait paths rather than inherent-method aliases.

After normal managed setup, build the separate recorder from the repository root:

```sh
python3 utf-8/0.7.6/publication/build-cli.py
```

Use Python 3.11 or newer. The builder checks the original tool store, both patches and the dependency lock, builds a disposable CLI copy offline, runs 25 scanner, 3 configuration and 7 report-composition tests, and prints its binary and receipt paths. It executes Cargo outside the repository's ancestor configuration without changing user homes. The checked-in receipt records the tested binary hash; rebuilding at a different path may produce a different binary hash.

`proofs-prepare.toml` restores the unchanged registry source and prepares the pinned Lean build in the recorder's isolated source snapshot. Set the managed `AENEAS_TOOL_CACHE`, `AENEAS_ARCHIVE_CACHE` and `AENEAS_LAKE_CACHE` inputs when reusing checked offline caches. Run the version-local verifier separately before recording.

Recording requires a clean, committed and pushed GitHub source snapshot. Keep the same publication checkout and package path through recording and upload. From its `.work/build/default/aarch64-apple-darwin/proofs` directory, use the separately built CLI:

```sh
"$CLI" run --manifest-path "$PACKAGE/Cargo.toml" \
  --proofs-config aeneas/profiles/default/proofs.toml -- lake build
```

Here `PACKAGE` is the absolute selected `utf-8/0.7.6` directory and `CLI` is the printed recorder binary. The CLI records standard Lake verification and theorem extraction; setup logs and repository scripts are excluded from SARIF. Once the recorded seven claims, preconditions, source commit and findings have been reviewed, publication uses the same package/configuration and recorded run ID:

```sh
"$CLI" publish --manifest-path "$PACKAGE/Cargo.toml" \
  --proofs-config aeneas/profiles/default/proofs.toml --run "$RUN_ID"
```

No login, push or publication is performed by the builder. Existing per-server CLI credentials are reused. `publish --dry-run` authenticates and may prepare a remote API catalogue; it is not a purely local check. Only the seven default-profile APIs are publication claims; the private storage helper and the conditional adapted-core contracts remain separately described limitations/evidence.
