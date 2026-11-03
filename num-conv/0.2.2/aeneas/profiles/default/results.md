# Verification results

The final offline managed run, `default-_3ft6xc2`, passed on
`aarch64-apple-darwin`. It checked all 180 concrete total-success contracts for
the five public conversion methods and their dispatchers. The audit passed for
193 theorems (180 concrete contracts, five aggregate API theorems and eight
helpers), and the five API mappings passed metadata checks. Source and harness
checks, native tests and fresh extraction comparison passed; input fingerprints
matched before and after the run. The mathematical guarantees and their scope
are described in [SPECIFICATION.md](../../../SPECIFICATION.md) and the report.
The extracted subject loads the unchanged release source as a module; equivalence
to normal linkage is not separately proved. Results for this target do not prove
other targets or pointer widths. The retained evidence is indexed in
[evidence/summary.json](evidence/summary.json) and
[evidence/archive.json](evidence/archive.json).

## Native tests

The final offline managed run used pinned Rust 1.91.1 on
`aarch64-apple-darwin` and passed its native test stage. It ran no upstream
unit tests, two added native tests, and 11 release documentation tests. The
added tests check boundary inputs for all 180 concrete instances and
exhaustively check the three truncation methods for `u16` to `u8` and `i16` to
`i8`. These tests are separate from formal proof and do not establish the
contracts for all inputs. The release library source is unchanged; the added
tests are a workspace adaptation recorded in the source lock.

## Findings

No num-conv defect was identified in this investigation.

## Verification infrastructure

The first managed run (`default-n4ixrhc3`) exposed an undefined variable in the
repository's Aeneas runner while checking generated model paths. The runner was
corrected by removing an unrelated backend-path substitution while retaining
target-placeholder resolution for generated model paths. Regression tests cover
matching and mismatching generated model contents. This is an issue in the local
verification infrastructure, not an observed defect in `num-conv`.
