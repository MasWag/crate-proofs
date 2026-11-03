# bs58 0.5.1 with unmodified Creusot

This independent workspace investigates the Base58 conversion cores and alphabet
constructor with Creusot 0.13.0. Its [specification](verification/specification.md)
defines the intended behavior; it is not evidence that the contracts have passed.
The accepted fresh run and precise scope are recorded in
[verification/results.md](verification/results.md).

The [proof crate](crate/src/lib.rs) contains a documented adaptation of four release
functions. [Correspondence](correspondence.md) identifies runtime changes and the
scope of the relationship to the unchanged registry release. In particular, the
encoder is specialized to byte slices. Native comparisons provide finite evidence
of matching behavior, not formal equivalence to the release.

Specifications were designed by Astra; Sol implements proof annotations and
mathematical helper proofs. Creusot and its shipped models remain unmodified.
The parent Aeneas profile and its historical proof evidence are separate.

The [native harness](verification/native/src/main.rs) compares success, errors,
complete output buffers, and fixed-array results with registry bs58 0.5.1.
It also reproduces the existing [checksum findings](verification/findings/README.md).
Checksum implementations, cryptographic guarantees, allocation, generic target
callbacks, and UTF-8 string target handling are outside this core investigation.

No release source fixes or upstream issue filings are performed here.
