# Adapted strict options contract

This profile reuses the independently authored pure state definitions in
`proofs/OptionsSpecs.lean`. The adapted `build_strict` body must return normally
with `buildState` equal to the builder's Boolean state for both possible states.
The adapted `SMALL_NUMBERS` and `LARGE_NUMBERS` constants must return normally
with `smallNumbers=true` and `largeNumbers=false`, respectively.

`verification/options-strict-harness/check-adaptation.py` checks that the Rust
source copy differs from the locked release at exactly the panic arm in
`build_strict`, plus independent Cargo workspace and native test wiring. The
unchanged release function is separately re-probed and remains unselected.
The checked `OptionsBuilder::build` contract in the direct release options
profile returns `Ok` for either state, supporting the argument that the
changed error arm is unreachable. Rust-to-Rust equivalence of the adapted body
to release code is not itself a Lean theorem.
