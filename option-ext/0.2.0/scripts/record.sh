#!/usr/bin/env bash
# Record only. Uploading is a separate, explicitly authorized CLI action.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="$(cd "$ROOT/../.." && pwd)"
source "$ROOT/scripts/env.sh"
bash "$ROOT/scripts/setup.sh"
export AENEAS_TOOL_CACHE="$REPO/.work/tools"
export AENEAS_ARCHIVE_CACHE="$ROOT/.work/cache"
export AENEAS_LAKE_CACHE="$ROOT/.work/selected-proofs/.lake/packages"
export RUSTUP_TOOLCHAIN=1.94.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export PATH="$ROOT/.work/selected-tools/cargo-proofs/bin:$PATH"
cd "$ROOT/.work/selected-proofs"
exec cargo proofs run --manifest-path "$ROOT/Cargo.toml" \
  --proofs-config aeneas/profiles/default/proofs.toml -- lake build
