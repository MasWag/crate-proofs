# Findings: bs58 0.5.1

These findings were reproduced against the unchanged release source, with both
optional features `check` and `cb58`. They are executable counterexamples and
source-review findings, not Lean proofs of the checksum implementations.

Run from the bs58 directory:

```sh
cargo run --locked --manifest-path evidence/reproduce-findings/Cargo.toml
```

All assertions must succeed. See `findings-output.log` for the observed output.
The reproducer uses the local bs58 package by path and independently computes
the checksums used to check the diagnostic fields.

## F1: checksum-only input can satisfy a requested version

Affected APIs: `decode::DecodeBuilder::with_check`, `as_cb58`, and the subsequent
`into_vec`/`onto` operations. Required features: `check` or `cb58` respectively.

- `bs58::decode("3QJmnh").with_check(Some(93)).into_vec()` returns `Ok([])`.
- `bs58::decode("45PJLL").as_cb58(Some(120)).into_vec()` returns `Ok([])`.

Both strings encode only the four checksum bytes for an empty unversioned
payload. There is no payload byte to serve as the requested version.
`decode_check_into` and `decode_cb58_into` reject fewer than four decoded bytes,
then subtract four and compare `output[0]` against the requested version. At
exactly four bytes, `output[0]` is the first checksum byte. Matching that byte
therefore passes the version check and returns zero payload bytes.

Consequence: success with `Some(version)` does not guarantee that returned data
contains that version. A caller relying on that guarantee can accept malformed
versioned input. No broader exploitability claim is made.

An existing upstream report describes this behavior:
[bs58-rs issue 132](https://github.com/Nullus157/bs58-rs/issues/132).
It was found during the later related-issue search; this work independently
reproduced the behavior and did not file that issue.

## F2: checked fixed-buffer decoding writes beyond the returned length

Affected API: `decode::DecodeBuilder::onto` with a fixed byte buffer and either
checksum feature enabled.

Encode payload `[42]` in the selected checksum mode. Decode it into a 16-byte
buffer initialized to `0xa5`. The call returns `Ok(1)`, but writes five bytes:
the payload and all four checksum bytes. The four bytes immediately after the
reported output prefix differ from their initial values; bytes beyond those
remain unchanged.

For Base58Check the first five output bytes are `[42, 255, 18, 44, 14]`.
For CB58 they are `[42, 95, 73, 79, 193]`.

The `onto` documentation promises that bytes after the final output byte are
untouched and describes the return value as the length written. The checked
helpers decode the payload plus checksum into the caller's buffer, then return
the payload length without restoring the suffix. This is an in-bounds contract
violation; the reproducer does not demonstrate memory unsafety. A one-byte
buffer for this one-byte payload also returns `BufferTooSmall`, because the
implementation needs scratch space for the checksum.

An existing upstream report matches this behavior:
[bs58-rs issue 133](https://github.com/Nullus157/bs58-rs/issues/133).
This work did not file that issue.

## F3: InvalidChecksum fields are reversed relative to their documentation

Affected API: `decode::Error::InvalidChecksum` under `check` or `cb58`.

Encode raw bytes `[42, 0, 0, 0, 0]` without a checksum mode, then decode using a
checksum mode. The last four input bytes are an intentionally incorrect given
checksum. The enum documents `checksum` as the given checksum and
`expected_checksum` as the calculated checksum. The actual error contains the
calculated checksum in `checksum` and `[0, 0, 0, 0]` in `expected_checksum`.

For Base58Check the calculated checksum is `[255, 18, 44, 14]`; for CB58 it is
`[95, 73, 79, 193]`. The reproducer checks these independently using SHA-256.
The Display implementation describes the actual field order, so the inconsistency
is specifically between the enum field documentation and the returned fields.
This affects programmatic diagnostics; checksum rejection itself still occurs.

## Scope and remediation status

No bs58 source fix has been applied. These findings do not imply that unchecked
Base58 arithmetic is incorrect. They also do not establish a complete absence of
other defects. Publication as proofs.rs findings remains pending the verification
report and account/repository access.
