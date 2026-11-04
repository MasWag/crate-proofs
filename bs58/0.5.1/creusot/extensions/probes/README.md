# Diagnostic boundary probes

Run `./run.sh` from this directory (or any directory). This creates a fresh
ignored raw evidence directory, proves the positive model bridges and trait
bodies, then saves expected failed proof diagnostics for contractless calls.
A successful diagnostic runner means its positive probes closed and its
negative probes stayed open; it does **not** mean all probe functions prove.

See `../../verification/extensions/model-boundaries.md`. The probe source's
`vec_utils.rs` intentionally copies the product helper file for isolated
investigation; the full extension runner must verify the integrated product.
The SHA dependency is only used to demonstrate current call boundaries; no
hash result property is assumed.
