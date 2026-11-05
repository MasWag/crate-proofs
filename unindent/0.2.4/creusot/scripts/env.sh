#!/usr/bin/env bash
source /home/lab8/mwaga/proof.rs/toolchain/creusot-env/env.sh
_version_creusot=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
export TMPDIR="$_version_creusot/.work/tmp"
export CARGO_TARGET_DIR="$_version_creusot/.work/target"
export PATH="/home/lab8/mwaga/proof.rs/toolchain/creusot-env/data/creusot/bin:$PATH"
unset _version_creusot
export RUSTUP_TOOLCHAIN=/home/lab8/mwaga/.rustup/toolchains/1.91.0-x86_64-unknown-linux-gnu
