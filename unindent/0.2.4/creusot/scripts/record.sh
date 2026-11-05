#!/usr/bin/env bash
set -euo pipefail
UNINDENT_CREUSOT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$UNINDENT_CREUSOT_ROOT"
source scripts/env.sh
mkdir -p "$TMPDIR"
UNINDENT_PROOFS_CLI="${CARGO_PROOFS_BIN:-$UNINDENT_CREUSOT_ROOT/../.work/selected-tools/cargo-proofs/bin/cargo-proofs}"
# Standard cargo-proofs records a fresh detached source checkout. Publication is
# a separate explicit command; no cached local sessions are submitted here.
exec "$UNINDENT_PROOFS_CLI" proofs run --manifest-path "$UNINDENT_CREUSOT_ROOT/Cargo.toml" -- \
  cargo creusot --no-cache \
  --why3find-arg=--no-autodetect-provers \
  --why3find-arg=-P --why3find-arg=z3,cvc5,alt-ergo \
  --why3find-arg=-j --why3find-arg=2 \
  --why3find-arg=--fast --why3find-arg=1 \
  --why3find-arg=--time --why3find-arg=10 \
  --why3find-arg=-d --why3find-arg=6
