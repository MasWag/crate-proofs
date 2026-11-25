#!/usr/bin/env bash
set -euo pipefail

crate_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
repo_root="$(cd "$crate_root/../.." && pwd)"
staging="$(mktemp -d "${TMPDIR:-/tmp}/toml-write-verification-XXXXXXXX")"
staged_crate="$staging/toml_write/0.1.2"
mkdir -p "$staged_crate"
cp "$repo_root/.gitignore" "$repo_root/rust-toolchain.toml" "$staging/"
cp -R "$repo_root/scripts" "$staging/scripts"
rsync -a --exclude=.work --exclude=target "$crate_root/" "$staged_crate/"
git -C "$staging" init -q

export AENEAS_TOOL_CACHE="${AENEAS_TOOL_CACHE:-$repo_root/.work/tools}"
export AENEAS_ARCHIVE_CACHE="${AENEAS_ARCHIVE_CACHE:-$crate_root/.work/cache}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-$staged_crate/.work/xdg-cache}"
if [[ -z "${AENEAS_LAKE_CACHE:-}" ]]; then
    existing_packages="$crate_root/.work/selected-proofs/.lake/packages"
    if [[ -d "$existing_packages" ]]; then
        export AENEAS_LAKE_CACHE="$existing_packages"
    fi
fi

printf 'Isolated workspace %s\n' "$staging"
exec bash "$staged_crate/scripts/verify.sh" "$@"
