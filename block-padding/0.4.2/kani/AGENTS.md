# Kani scope

This is an independent Kani workspace for block-padding 0.4.2. Use Kani 0.68.0 and the locked real dependencies; do not activate Aeneas or Creusot here. Preserve original release runtime bodies and the annotation-only correspondence check. Keep all ordinary safety checks and unwinding assertions enabled, with no stubs.

Claims are limited to U16, detached lengths 0..32, block counts 0..2, and the stated padding-position and variant premises. Only PaddedData::unwrap is a recorded contract claim; the other 24 ordinary harnesses are supplementary bounded evidence. Specification/review is assigned to Astra, implementation to Sol. The user explicitly authorized publication of successful additional verification to proofs.rs.
