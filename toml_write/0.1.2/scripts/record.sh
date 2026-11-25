#!/usr/bin/env bash
# Record the selected report with the pinned CLI and standard Lake build.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
repo="$(cd "$root/../.." && pwd)"
bash "$root/scripts/setup.sh" "$@"

export AENEAS_TOOL_CACHE="${AENEAS_TOOL_CACHE:-$repo/.work/tools}"
export AENEAS_ARCHIVE_CACHE="${AENEAS_ARCHIVE_CACHE:-$root/.work/cache}"
export AENEAS_LAKE_CACHE="${AENEAS_LAKE_CACHE:-$root/.work/selected-proofs/.lake/packages}"
export RUSTUP_TOOLCHAIN=1.94.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export PATH="$root/.work/selected-tools/cargo-proofs/bin:$PATH"
if [[ ${1:-} == --offline ]]; then
    export CARGO_NET_OFFLINE=true
fi
cd "$root/.work/selected-proofs"
exec cargo proofs run --manifest-path "$root/Cargo.toml" \
    --proofs-config aeneas/profiles/default/proofs.toml -- lake build
