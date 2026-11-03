#!/usr/bin/env bash
CREUSOT_OPTION_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CREUSOT_OPTION_WORK="${CREUSOT_OPTION_CACHE:-$CREUSOT_OPTION_ROOT/.work}"
export CREUSOT_OPTION_ROOT CREUSOT_OPTION_WORK
export CARGO_HOME="$CREUSOT_OPTION_WORK/cargo"
export CREUSOT_DATA_HOME="$CREUSOT_OPTION_WORK/data"
export PATH="$CARGO_HOME/bin:/opt/homebrew/opt/rustup/libexec/bin:$PATH"
export RUSTUP_TOOLCHAIN=nightly-2026-06-22
export CARGO_BUILD_JOBS=4
