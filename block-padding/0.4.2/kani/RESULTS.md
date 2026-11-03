# Kani verification results

This independent workspace checks the unmodified release implementation bodies with Kani-only contracts and harnesses. The [specification](../verification/alternative-specification.md) defines the intended observations and finite domains. A local macOS arm64 run passed all 25 harnesses with no failures; its ignored local log is [.work/all.log](.work/all.log). The later isolated recording reruns these checks.

| Scope | Instances and bounds | Status |
|---|---|---|
| `PaddedData::unwrap` contract | `Pad`, U16, zero through two preceding blocks, arbitrary bytes; returned pointer, length, block bytes and tail bytes | Local run passed; the only intended proofs.rs mapped claim |
| Typed `pad` and `unpad` | Six schemes, U16, arbitrary bytes, valid pad positions; exact padding and decode result | 12 ordinary bounded harnesses passed locally |
| `pad_detached` | Six schemes, U16, arbitrary input bytes and length 0–32; variants, prefix pointer and bytes, tail | Six ordinary bounded harnesses passed locally |
| `unpad_blocks` | Six schemes, U16, arbitrary bytes, zero through two blocks; acceptance, errors and returned prefix | Six ordinary bounded harnesses passed locally |

The ordinary harnesses supplement the contract claim; they are not mapped proofs.rs claims. NoPad and Error `unwrap` arms, invalid pad positions, other block sizes, longer inputs, arbitrary downstream implementations, and complete Rust undefined-behavior or cryptographic security claims are outside the checked scope. The actual locked `hybrid-array` 0.4.15 and `typenum` 1.20.1 are used without a replacement shim. Results depend on Kani, CBMC, compiler and standard-library models. Native tests are separate from bounded verification.

The local native test run separately passed six doctests; see the ignored local [.work/native-tests.log](.work/native-tests.log). The Kani contract and the supplementary harnesses use an unwind bound of 35.

The [published Kani report](https://proofs.rs/report/17) records one bounded `unwrap` claim. The [compact evidence receipt](evidence/summary.json) distinguishes the successful fresh 25-harness proof from its oversized recording, and the later successful one-contract recording. Full logs and original SARIF are retained in the [local-only archive](evidence/archive.json), under `.work/evidence-archives`; hashes alone do not provide a public download. The recorded source commit remains `e6f38cca41b323b1fcfba86d4fffc8fdd99c96b4`.
