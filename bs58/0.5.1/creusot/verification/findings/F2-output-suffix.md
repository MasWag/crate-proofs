# F2: checked decoding modifies bytes beyond its returned length

## Identity and classification

- Crate/version: bs58 0.5.1, unchanged registry release.
- Component: fixed-buffer checked decoder; kind: implementation-bug.
- Confidence: reproduced-at-pinned-inputs; resolution: open in the tested release.
- Previously reproduced in the Aeneas trial; independently rerun in this trial.
- Related upstream report recorded previously: [issue 133](https://github.com/Nullus157/bs58-rs/issues/133). Current upstream fix status was not checked.

## Expected and observed behavior

The `onto` documentation promises that bytes after the final output byte remain
untouched and describes the returned value as the length written. With `check`:

```rust
let encoded = bs58::encode([42]).with_check().into_string();
let mut output = [0xa5; 16];
assert_eq!(bs58::decode(encoded).with_check(None).onto(&mut output), Ok(1));
assert_eq!(&output[..5], &[42, 255, 18, 44, 14]);
```

These assertions succeed. Four bytes beyond the reported prefix have changed.
CB58 has the same behavior, with prefix `[42, 95, 73, 79, 193]`. Bytes after that
prefix remain unchanged in this example. The helpers decode payload plus checksum
into the caller's buffer, then return only the payload length.

This is an in-bounds output-contract violation, not demonstrated memory unsafety.

## Reproduction and evidence

Run the [native harness](../native/src/main.rs) with `--findings` as described in
[the index](README.md). It asserts both modified checksum suffixes and the unchanged
remaining bytes. Source identity is pinned by the parent `source.lock.json` and
native Cargo.lock. Current run/log hashes are in the native evidence summary;
raw logs remain local in ignored `.work/`.

Checksum paths are outside the selected core proof. No release fix was applied.
