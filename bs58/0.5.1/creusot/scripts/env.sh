#!/usr/bin/env bash
# Explicit activation; this changes only the shell that sources this file.
_bs58_creusot_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
if [[ ! -f "$_bs58_creusot_root/.work/tools/env.sh" ]]; then
  echo "Missing pinned tool environment; see verification/toolchain-setup.md." >&2
  unset _bs58_creusot_root
  return 1
fi
source "$_bs58_creusot_root/.work/tools/env.sh"
export RUSTUP_TOOLCHAIN=nightly-2026-06-22
export WHY3CONFIG="$XDG_DATA_HOME/creusot/creusot_why3.conf"
export DUNE_DIR_LOCATIONS="why3find:lib:$XDG_DATA_HOME/creusot/share/why3find"
unset _bs58_creusot_root
