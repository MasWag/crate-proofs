# UTF8-TOOL-001: Generated Lean string contains invalid escapes

This is a verifier tool defect observation, not a crate behavior finding.
The unchanged release defines the replacement character as Rust `"\u{FFFD}"`.
The generated Lean for the `LossyDecoder` drop probe instead contains
`toStr "\239\191\189"`, which the pinned Lean parser rejects. This prevents
checking the unmodified generated drop model; it does not show a defect in the
Rust replacement character.

On the pinned profile and host, reproduce from the repository root with:

```sh
/opt/homebrew/bin/python3 utf-8/0.7.6/scripts/probe-methods.py
```

The local-only ignored evidence `.work/boundary-probes/methods-8r0owcfb/3/`
contains `Utf8.lean` and `lean.log`. The latter reports `invalid escape sequence`
at line 27, column 43, followed by a warning that the declaration uses `sorry`.
The partial generated output is not a proof. Tool revisions are recorded in
`aeneas/profiles/default/toolchain.lock.json`; no upstream report or fix is
claimed.
