# `build_strict` extraction investigation

The unchanged release `OptionsBuilder::build_strict` remains outside the
accepted Options inventory. A fresh probe uses
`verification/original-options-extraction.json` and
`scripts/check-original-options-blocker.py`. Charon succeeds, then clean
Aeneas reports an internal error at release `src/options.rs:146:15-20` in
`interp/Interp.ml:629`, the `Err(error) => core::panic!(...)` arm. The constants
`SMALL_NUMBERS` and `LARGE_NUMBERS` call this function and are likewise
excluded. The repro preserves logs under `.work/original-options-*/output`.

The independent workspace at `verification/options-strict-harness` is a copy
of the locked release source with only that arm changed to
`Err(_error) => self.build_unchecked()`. The package/library names, workspace
declaration, and native comparison test are the disclosed Cargo additions.
`check-adaptation.py` compares the complete copied file inventory and source
bytes against the locked release, verifies the exact arm and manifest changes,
and compares the locked lexical-util checksum. Clean Aeneas regenerates
`build_strict`, `build`, `build_unchecked`, `SMALL_NUMBERS`, and `LARGE_NUMBERS`
from this adapted copy. Three maintained Lean theorems in the
`options_strict_adapted` profile prove normal results for both builder states
and both constants. Their axiom audit permits only `propext`,
`Classical.choice`, and `Quot.sound`. Two native tests compare the adapted
observations to the unmodified release.

This adapted profile is **not** a proof of the original `build_strict` body.
The independently checked release `build` contract returns `Ok` for
every builder state, making the replaced arm unreachable under that contract.
The relationship between the copied Rust body and release Rust is still a
separate source-adaptation argument. Recorder mappings identify the adapted
crate rather than the release API. A wrapper
around the unmodified release API was also tried; Aeneas generated opaque
external `OptionsBuilder` and `build` axioms, so that model was rejected.
