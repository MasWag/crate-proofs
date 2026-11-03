#!/usr/bin/env bash
# The SDK27 weak imports exist at link time but not on this macOS26 runtime.
# These Autoconf answers select OCaml's existing portable implementations.
export ac_cv_func_pipe2=no
export ac_cv_func_dup3=no
export ac_cv_func_accept4=no
export DUNE_CACHE=disabled
# Prefer working rustup proxies over an independent Homebrew Rust installation.
if [[ "$(uname -s)" == Darwin ]] && command -v brew >/dev/null 2>&1; then
  BREW_BIN="$(command -v brew)"
  if [[ "$(uname -m)" == arm64 && -x /opt/homebrew/bin/brew ]]; then
    BREW_BIN=/opt/homebrew/bin/brew
  fi
  RUSTUP_PREFIX="$("$BREW_BIN" --prefix rustup)"
  export PATH="$RUSTUP_PREFIX/libexec/bin:$(dirname "$(command -v python3.11 || command -v python3)"):$PATH"
fi
PYTHON3="${PYTHON3:-$(command -v python3.11 || command -v python3)}"
export PYTHON3
"$PYTHON3" -c 'import sys; assert sys.version_info >= (3, 11), "Python >=3.11 required"'
