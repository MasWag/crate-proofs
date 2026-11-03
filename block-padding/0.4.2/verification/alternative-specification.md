# Alternative-verifier contracts

Specification responsibility: Astra specification/review agent. Implementation
responsibility: Sol implementation agent. The primary reviews final contracts,
commands, evidence, and claims. This document defines targets; it records no
successful verification. It supplements rather than weakens `SPECIFICATION.md`.

## Selected target and finite domains

Check calls into the unchanged crates.io `block-padding` 0.4.2 implementation,
including its concrete `hybrid-array` dependency bodies. A suitable initial Kani
scope is `Array<u8, U16>` (`B = 16`), arbitrary byte values, detached input lengths
`0 <= L <= 32`, and block lists with `0 <= K <= 2`. These bounds include empty,
partial, aligned, and two-block inputs, and zero trimming across block boundaries.
They do not establish other block sizes, larger inputs, generic `ArraySize`
implementations, or all-length correctness. Each published bound must match the
actual harness; additional sizes require separately checked instantiations.

Use independent nondeterministic bytes for every backing-storage byte. Select
lengths nondeterministically within the stated bounds. Never restrict decoded
inputs to padded outputs: malformed padding belongs to the decoder contract.
Assumptions may constrain only the stated input domain, not implementation
outputs, expected variants, the dependency's behavior, or the desired property.

## Independent byte predicates

For a sequence `x` of length `n`, let `trim(x)` be the largest `t <= n` such that
`t = 0` or `x[t-1] != 0`; equivalently, delete its maximal trailing zero suffix.
Define `decode(P, x)` as a partial retained length:

| Scheme | Retained length / rejection condition |
|---|---|
| ZeroPadding | `trim(x)`; always accepts |
| NoPadding | `n`; always accepts |
| Pkcs7 | Put `c = x[n-1]`. Accept `n-c` iff `1 <= c <= n` and every byte at indices `n-c .. n` equals `c`. |
| Iso10126 | Put `c = x[n-1]`. Accept `n-c` iff `1 <= c <= n`; no other suffix condition. |
| AnsiX923 | Put `c = x[n-1]`. Accept `n-c` iff `1 <= c <= n` and all bytes at indices `n-c .. n-1` are zero. |
| Iso7816 | Accept `t` iff `t < n`, `x[t] = 128`, and all subsequent bytes are zero; reject if no such index exists. |

The count-byte predicates here are used only with `n = 16`; they make no empty
raw-decoder claim. Compute predicates directly from bytes, without calling the
crate's raw algorithms or using the same library flatten/chunk operation as the
expected-value oracle. Independent simple loops are acceptable specifications.

For valid typed pad inputs, every output byte at index `i < p` equals its original
value. The suffix is: zeros for ZeroPadding; unchanged original bytes for
NoPadding; repetitions of `B-p` for Pkcs7 and Iso10126; zeros then final count
`B-p` for AnsiX923; byte 128 then zeros for Iso7816. Positions satisfy `p <= B`
for ZeroPadding and NoPadding and `p < B` for the other four schemes.

## API obligations

For each of all six concrete schemes:

* **Typed `pad::<U16>`:** all-byte result equals the preceding padding predicate
  for every arbitrary initial block and valid position. Complete execution must
  satisfy the verifier's enabled safety checks without panic.
* **Typed `unpad::<U16>`:** `Ok` occurs exactly when `decode` accepts; `Err`
  occurs exactly when it rejects. An accepted slice has the exact retained
  length, all original prefix bytes, and the original block's starting pointer.
* **`pad_detached::<U16>`:** let `q = L / B` and `r = L % B`. Full blocks have
  count `q`, every byte equals input byte `j*B+i`, and their starting pointer
  equals the input starting pointer, including zero-length returned slices.
  ZeroPadding returns `NoPad` iff `r = 0`; otherwise `Pad` with original tail
  bytes followed by zeros. NoPadding returns `NoPad` iff `r = 0`, otherwise
  `Error`. The other four schemes always return `Pad`, with original tail bytes
  followed by their exact scheme-specific suffix, even for empty/aligned input.
  The source input remains unchanged. `Pad` therefore has a freshly padded tail
  block in addition to all `q` existing full blocks.
* **`unpad_blocks::<U16>`:** define the flattened input independently as
  `x[j*B+i] = blocks[j][i]`. ZeroPadding accepts retained length `trim(x)` and
  NoPadding accepts `K*B`, including `K = 0`. The other four return `Err` for
  `K = 0`; otherwise acceptance is exactly acceptance of the final block under
  `decode`, with retained length `(K-1)*B + decode(last)`. Accepted output has
  every original flattened prefix byte and the starting pointer of the block
  list cast to a byte pointer. Rejecting calls return `Err`. Earlier full blocks
  need not themselves contain valid padding.

`PaddedData::unwrap` can additionally be checked for arbitrary `Pad` contents:
returned blocks retain their pointer, length and bytes, and the owned tail has
every original byte. Its `NoPad` and `Error` panic arms are separate obligations;
an ordinary successful harness for `Pad` proves neither. Likewise, invalid pad
positions and zero/oversized block sizes are excluded from the above successes.

## Representation and proof boundary

Do not replace `hybrid-array` with a hand-written array shim, assume conversion
correctness, or stub the public API under verification. Its checked instance
must include real `Array::as_slice`, `as_mut_slice`, `slice_as_chunks`, and
`slice_as_flattened` bodies and their unsafe slice/pointer operations. In local
dependency version 0.4.15, `Array` is `repr(transparent)`, chunking asserts a
nonzero size, and flattening uses checked multiplication before constructing a
slice from its pointer. These source observations motivate the obligations;
they do not themselves prove the dependency or justify all `ArraySize` values.

Keep Kani/Rust/CBMC semantics, standard-library models, compiler translation,
and any unsupported-feature allowances explicit in the report. Record exact
tool versions, Cargo lockfile, source identity, features, target, harness list,
commands, and full outcomes. Retain overflow, bounds, pointer/memory, panic, and
unwinding-assertion checks. An insufficient unwind bound is a failed proof;
disabling unwinding assertions would support only an execution-depth claim and
does not discharge these finite-domain contracts. Review unsupported-operation
diagnostics and unexpected vacuity. Native tests remain separate evidence.

Passing the harnesses proves these properties for their finite domains under
the verifier's checked semantics. It does not turn this supplementary result
into a general theorem for arbitrary block size or input length, nor into an
independent proof of the entire dependency or public trait implementations
provided by downstream crates.
