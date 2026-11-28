# leb128fmt 0.1.0

This version workspace targets the registry release identified by `source.lock.json`. The Aeneas profile specifies the codec families in `aeneas/profiles/default/specification.md`; its theorem inventory and results distinguish proved operations from remaining obligations. Native tests and observed failures are separate from formal proofs.

From the repository root, prepare the pinned inputs and run the managed verification:

```sh
bash leb128fmt/0.1.0/scripts/setup.sh
bash leb128fmt/0.1.0/scripts/verify.sh --offline
```

For an already populated cache, setup also accepts `--offline`. The selected profile's results and tool lock describe the run, dependencies, and supported targets.

The following local findings are issue-ready observations, not upstream reports:

- [LEB128FMT-001](verification/findings/LEB128FMT-001.md): narrow unsigned decoding accepts an out-of-range value.
- [LEB128FMT-002](verification/findings/LEB128FMT-002.md): signed slice encoders accept an out-of-range value.
- [LEB128FMT-003](verification/findings/LEB128FMT-003.md): fixed unsigned array encoding panics at width seven.
- [LEB128FMT-004](verification/findings/LEB128FMT-004.md): decoders mishandle continuation at a seven-bit width.

Their issue-ready titles and bodies are in `verification/findings.toml`. This is an editorial draft, not a complete report configuration: the pinned reporting CLI does not accept finding entries. Nothing has been filed or published.
