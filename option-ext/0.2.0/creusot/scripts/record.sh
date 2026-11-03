#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
bash "$ROOT/scripts/setup.sh" --offline
export CREUSOT_OPTION_CACHE="$CREUSOT_OPTION_WORK"
export CREUSOT_PROOFS_RS_STORE="${CREUSOT_PROOFS_RS_STORE:-$ROOT/../.work/selected-tools}"
export PATH="$CREUSOT_PROOFS_RS_STORE/cargo-proofs/bin:$PATH"
cd "$ROOT"
# Refuse ambient Cargo configuration that would mutate the normalized lock.
cargo metadata --locked --offline --format-version 1 --no-deps >/dev/null
exec cargo proofs run --manifest-path "$ROOT/Cargo.toml" -- cargo creusot --no-cache --why3session
