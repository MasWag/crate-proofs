# num-conv 0.2.2 verification

This workspace investigates the crates.io `num-conv` 0.2.2 release with
Aeneas and Lean. The unchanged release library is identified by
[source.lock.json](source.lock.json). The verification-only harness loads the unchanged release source as a Rust
module and calls its public conversion methods for each supported concrete
integer pair. This repackaging supports extraction; equivalence to the normally
linked release is not separately proved. The native test target is an addition
to the workspace manifest.

[SPECIFICATION.md](SPECIFICATION.md) defines the intended 180 total-success
contracts for widening, deprecated extension, wrapping, saturating and checked
truncation. It is an intended scope, not a claim that every contract has been
proved. Current results, including the status of managed acceptance and separate
native tests, are in [results.md](aeneas/profiles/default/results.md). The
profile and pinned tools are under [aeneas/profiles/default](aeneas/profiles/default).

From the repository root, `num-conv/0.2.2/scripts/setup.sh` prepares the managed
toolchain and `num-conv/0.2.2/scripts/verify.sh` runs the managed verification.
The profile currently targets `aarch64-apple-darwin`; another target is not
covered by a successful run on this one. No publication is implied by these
local artifacts.
