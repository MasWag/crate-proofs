#!/usr/bin/env bash
UNINDENT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export UNINDENT_ROOT
export PATH="$UNINDENT_ROOT/.work/selected-tools/cargo-proofs/bin:$UNINDENT_ROOT/.work/selected-tools/aeneas/bin:$UNINDENT_ROOT/.work/selected-tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=1.94.1
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export CARGO_TARGET_DIR="$UNINDENT_ROOT/.work/build/native"
