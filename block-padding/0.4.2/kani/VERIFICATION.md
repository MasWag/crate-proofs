# Kani supplementary verification

This independent Cargo workspace derives `src/lib.rs` byte-for-byte from the
restored crates.io release, adding only Kani contract attributes to the existing
`PaddedData::unwrap` and a `cfg(kani)` verification module. Run
`python3 scripts/prepare.py --check` to check the derivation. The release source
hash is pinned in that script. Real hybrid-array 0.4.15 and typenum 1.20.1 are
locked; neither is replaced or stubbed.

The 24 ordinary proof harnesses check all six algorithms' typed padding, typed
unpadding, detached padding, and block-list unpadding against independent byte
predicates. Scope is U16 arrays, arbitrary bytes, all valid padding positions,
0..32 detached bytes, and 0..2 blocks. The unwrap contract additionally checks
Pad contents with U16 arrays and 0..2 blocks: exact original blocks pointer,
length and bytes, and all tail bytes. It excludes both panic variants.

Use `scripts/verify.sh` with Kani 0.68.0 / CBMC 6.11.0; the wrapper selects offline
Cargo resolution and checks the source derivation. It does not activate an Aeneas
or Creusot environment. All normal safety checks and unwinding assertions remain
enabled, with unwind 35. No stubs, loop contracts, or dependency contracts are used.

The recorded `proof_for_contract` probes could not target these generic trait
methods in Kani 0.68.0, including concrete overrides; the compiler diagnostic is retained in ignored
`.work/probes/generic-trait-contract.log`. Therefore the 24 ordinary harnesses
provide supplementary local bounded evidence; only the inherent unwrap contract
is eligible for discovery by the pinned proofs CLI. This is a recording and
verifier contract-support limitation, separate from ordinary harness success.

This does not establish arbitrary array sizes, arbitrary input lengths, downstream
Padding implementations, panic arms, formatting/derives, or the complete external
array dependency. The existing Aeneas raw-algorithm results remain separate.

The run emitted unsupported `caller_location` and foreign-function diagnostics. Kani is configured to fail if those operations are reached; they did not cause failures in the passed harnesses.

The version-local [recorder patch](verification/proofs-cli-generic-inherent.patch) and [tool pin](verification/proofs-cli-tool.json) fix discovery of an inherent contract on a nominal generic owner; they do not change Kani, the compiler, or the proof.

On a fresh checkout, restore the pinned release source from the repository root without setting up Aeneas tools:

```sh
python3.11 scripts/aeneas-manage.py setup block-padding/0.4.2 --sources-only
```

Then `python3 scripts/prepare.py --check` can check the Kani source derivation from this workspace.
