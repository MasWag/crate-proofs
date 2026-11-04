# Optional target boundary diagnostics

This is diagnostic evidence only, outside the extension product proof inputs and target count. No application body, Creusot source, or standard model was changed. The authoritative release bodies are `../.work/source/src/encode.rs` and `decode.rs` relative to the Creusot workspace (the parent version's `.work/source`).

`extensions/optional-probes/run.sh` compiles ten concrete byte-container probes using pinned Creusot 0.13.0, upstream revision `318615be3b8bbc60d1f6d52469ba5c0bdebed4f1`, cached smallvec 1.16.1 and tinyvec 1.13.3. Dependencies resolve offline; this run has no cache-miss execution limitation. Tinyvec enables `alloc` and the release's required `grab_spare_slice` feature. The initial omitted-feature diagnostic is retained separately in ignored `compile-missing-feature.log`; it is superseded by the successful compile.

Reproduce from the repository root:

```sh
bash bs58/0.5.1/creusot/extensions/optional-probes/run.sh
```

The compile succeeded. Each call emitted `calling external function ... with no contract will yield an impossible precondition`; each generated Coma file contains `{[%#slib] false} any` at the callee boundary. Thus a whole proof run is unnecessary to diagnose these exact open calls. Successful compilation is not proof.

| Release target used by encode/decode | Concrete probe | Missing callee contracts |
|---|---|---|
| `smallvec::SmallVec<A>` | `SmallVec<[u8;32]>` | `resize`, `truncate`, mutable `IndexMut<RangeFull>::index_mut` for `&mut v[..]` |
| `tinyvec::ArrayVec<A>` | `ArrayVec<[u8;32]>` | `grab_spare_slice_mut`, `set_len` |
| `tinyvec::SliceVec<'_,u8>` | `SliceVec<'_,u8>` | `grab_spare_slice_mut`, `set_len` |
| `tinyvec::TinyVec<A>` | `TinyVec<[u8;32]>` | `resize`, `truncate`, mutable `IndexMut<RangeFull>::index_mut` for `&mut v[..]` |

These are narrow boundaries, not claims that verification of these crates is impossible. A faithful target proof needs contracts connecting length/capacity, prefix preservation, initialized spare storage, returned mutable slices and final resolved contents. Fixed-capacity targets also need the callback result bounded by available spare length before `set_len`. The probes deliberately add neither external specifications nor replacement container implementations. Other calls in the release implementations (such as `len`) are not positively certified by this audit.

Raw output, generated Coma, source hashes and revision are under ignored `.work/extensions/optional-probes/`. Diagnostic Rust, dependency lock and reproduction command are retained in `extensions/optional-probes/`. No optional target is promoted into verified coverage by this ledger.

## Generic private encoder

Release `encode.rs:434` takes only `I: Clone + IntoIterator<Item=&u8>` and performs the arithmetic pass over `input.clone()`, then counts leading zeroes over `input.into_iter()`. The stock `creusot-std/src/std/clone.rs` generic `Clone::clone` declaration has no postcondition relating the cloned value to the original. Stock `std/iter.rs` gives `IteratorSpec::produces`, `completed` and the `next` result relation; it does not establish a generic law equating these two `IntoIterator` traversals. The blanket `IntoIterator for I: Iterator` contract returns the same iterator but does not supply a clone law.

Therefore a generic proof against one input byte sequence must be qualified by semantic laws: both original and cloned inputs convert to finite iterators producing the same ordered byte values, with an appropriate completion/termination argument (and stable referenced bytes during both traversals). Rust's original `Clone + IntoIterator` bounds alone do not imply these laws: user implementations can produce different sequences or fail to terminate. One may instead prove a suitable concrete iterator instantiation whose existing contracts justify these properties. This audit introduces no new trait, axiom, model or implementation and does not claim the unrestricted original generic signature has that stronger behavior.
