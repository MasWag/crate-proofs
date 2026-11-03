# Findings for bs58 0.5.1

The native harness independently reproduced the three checksum observations from
the earlier Aeneas trial. They are retained under the same F1–F3 identities below;
they are not three newly discovered defects. No additional unchecked-core defect
has been established by this trial. Failure to prove a contract is not a bug.

- [F1: a checksum byte can satisfy an expected version](F1-checksum-only-version.md)
- [F2: checked decoding modifies bytes beyond its returned length](F2-output-suffix.md)
- [F3: checksum error fields disagree with their documentation](F3-error-fields.md)

Run the Rust reproductions from this workspace with the native environment:

```sh
cargo run --locked --manifest-path verification/native/Cargo.toml -- --findings
```

Success means the assertions reproduced the discrepancies. The harness pins the
unchanged registry package `bs58 = 0.5.1` with `check` and `cb58`; its Cargo.lock
records the release checksum. These are ordinary executable observations, not
formal verification of the checksum paths. They do not falsify unchecked Base58
conversion contracts.

The [prior public report](https://proofs.rs/report/13) contains the earlier findings.
No upstream filing or source fix is performed by this trial. See the current
results and native evidence summary for reproduction hashes and log identities.
