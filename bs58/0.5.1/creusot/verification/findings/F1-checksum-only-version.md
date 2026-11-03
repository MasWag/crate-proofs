# F1: a checksum byte can satisfy an expected version

## Identity and classification

- Crate/version: bs58 0.5.1, unchanged registry release.
- Component: checksum decoder; kind: implementation-bug.
- Confidence: reproduced-at-pinned-inputs; resolution: open in the tested release.
- Previously reproduced in the Aeneas trial; independently rerun in this trial.
- Related upstream report recorded previously: [issue 132](https://github.com/Nullus157/bs58-rs/issues/132). Current upstream fix status was not checked.

## Expected and observed behavior

`with_check(Some(version))` and `as_cb58(Some(version))` request a version byte.
A successful result should therefore contain that byte before the checksum.
Instead, an input containing only four checksum bytes can pass the version check:

```rust
assert_eq!(bs58::decode("3QJmnh").with_check(Some(93)).into_vec(), Ok(vec![]));
assert_eq!(bs58::decode("45PJLL").as_cb58(Some(120)).into_vec(), Ok(vec![]));
```

Both assertions succeed, reproducing the discrepancy. The decoded input has no
payload/version byte. The helpers check for at least four bytes, subtract the
checksum length, then compare `output[0]` with the requested version. For exactly
four bytes, that location belongs to the checksum. No broader exploit is asserted.

## Reproduction and evidence

Enable `check` and `cb58`; run the [native harness](../native/src/main.rs) with
`--findings` as described in [the index](README.md). It checks both modes against
the unchanged registry release. Source identity is pinned by the parent
`source.lock.json` and the native Cargo.lock. Current run/log hashes are in the
native evidence summary; raw logs remain local in ignored `.work/`.

Checksum paths are outside the selected core proof. No release fix was applied.
