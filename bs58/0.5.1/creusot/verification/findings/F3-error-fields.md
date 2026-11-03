# F3: checksum error fields disagree with their documentation

## Identity and classification

- Crate/version: bs58 0.5.1, unchanged registry release.
- Component: `decode::Error::InvalidChecksum`; kind: documentation-mismatch.
- Confidence: reproduced-at-pinned-inputs; resolution: open in the tested release.
- Previously reproduced in the Aeneas trial; independently rerun in this trial.
- Upstream report/fix status: not checked in this trial; no issue filed here.

## Expected and observed behavior

The enum field documentation describes `checksum` as the given checksum and
`expected_checksum` as the calculated checksum. The returned fields have the
opposite contents:

```rust
let encoded = bs58::encode([42, 0, 0, 0, 0]).into_string();
assert_eq!(
    bs58::decode(encoded).with_check(None).into_vec(),
    Err(bs58::decode::Error::InvalidChecksum {
        checksum: [255, 18, 44, 14],
        expected_checksum: [0, 0, 0, 0],
    }),
);
```

This assertion succeeds. The given checksum is all zeros; the other value is
calculated from the payload `[42]`. CB58 similarly returns calculated
`[95, 73, 79, 193]` in `checksum`. The Display implementation follows the actual
field order. Checksum rejection still occurs; the discrepancy affects the enum's
documented programmatic diagnostics.

## Reproduction and evidence

Run the [native harness](../native/src/main.rs) with `--findings` as described in
[the index](README.md). It independently calculates the checksums using SHA-256
and checks both modes. Source identity is pinned by the parent `source.lock.json`
and native Cargo.lock. Current run/log hashes are in the native evidence summary;
raw logs remain local in ignored `.work/`.

Checksum paths are outside the selected core proof. No release fix was applied.
