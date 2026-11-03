#!/usr/bin/env bash
# Use rustup proxies and a target-local Cargo cache. Rustup and Elan homes remain
# caller-owned. setup.sh separately isolates tool-build Cargo configuration.
OPTION_EXT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export CARGO_HOME="$OPTION_EXT_ROOT/.work/cargo-home"
mkdir -p "$CARGO_HOME"
export PATH="$OPTION_EXT_ROOT/.work/gnu-make/bin:$PATH"
if [[ -d /opt/homebrew/opt/rustup/libexec/bin ]]; then
  export PATH="/opt/homebrew/opt/rustup/libexec/bin:$PATH"
fi
if command -v python3.11 >/dev/null 2>&1; then
  export OPTION_EXT_PYTHON="$(command -v python3.11)"
else
  export OPTION_EXT_PYTHON="$(command -v python3)"
fi
export ac_cv_func_pipe2=no ac_cv_func_dup3=no ac_cv_func_accept4=no
export DUNE_CACHE=disabled
