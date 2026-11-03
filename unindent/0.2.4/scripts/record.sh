#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
env -u CARGO_TARGET_DIR bash "$ROOT/scripts/setup.sh"
export AENEAS_TOOL_CACHE="${AENEAS_TOOL_CACHE:-$(cd "$ROOT/../../.work/tools" && pwd)}"
export AENEAS_ARCHIVE_CACHE="${AENEAS_ARCHIVE_CACHE:-$ROOT/.work/cache}"
source "$ROOT/scripts/env.sh"
HOST="$(rustc -vV | sed -n 's/^host: //p')"
export AENEAS_LAKE_CACHE="${AENEAS_LAKE_CACHE:-$ROOT/.work/build/default/$HOST/proofs/.lake/packages}"
CLI="${CARGO_PROOFS_BIN:-$ROOT/.work/selected-tools/cargo-proofs/bin/cargo-proofs}"
ARGS=(--manifest-path "$ROOT/Cargo.toml" --proofs-config aeneas/profiles/default/proofs.toml)
cd "$ROOT/.work/build/default/$HOST/proofs"
exec "$CLI" proofs run "${ARGS[@]}" -- lake build
