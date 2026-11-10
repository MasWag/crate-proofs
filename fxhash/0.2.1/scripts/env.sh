#!/usr/bin/env bash
FXHASH_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export CARGO_HOME="${CARGO_HOME:-$FXHASH_ROOT/.work/cargo-home}"
mkdir -p "$CARGO_HOME"
if [[ -d /opt/homebrew/opt/rustup/libexec/bin ]]; then export PATH="/opt/homebrew/opt/rustup/libexec/bin:$PATH"; fi
export ac_cv_func_pipe2=no ac_cv_func_dup3=no ac_cv_func_accept4=no DUNE_CACHE=disabled
