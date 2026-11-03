#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT/scripts/env.sh"
if [[ "${1:-}" == "--offline" ]]; then export CARGO_NET_OFFLINE=true; export CREUSOT_SETUP_OFFLINE=1; fi
export CREUSOT_OPAM_PREFIX="${CREUSOT_OPAM_PREFIX:-$HOME/.creusot/_opam}"
export CREUSOT_PROVER_DIR="${CREUSOT_PROVER_DIR:-$HOME/Library/Application Support/creusot.creusot/bin}"
mkdir -p "$CREUSOT_OPTION_WORK" "$ROOT/.work"
python3.11 - "$ROOT" <<'PY'
import os,sys
from pathlib import Path
r=Path(sys.argv[1]);sys.path.insert(0,str(r.parents[2]/'scripts'))
from aeneas_management import source
cache=r/'.work/cache'; shared=Path(os.environ['CREUSOT_OPTION_WORK'])/'cache'
if cache!=shared and not cache.exists():cache.symlink_to(shared,target_is_directory=True)
source.restore(r,offline=os.environ.get('CREUSOT_SETUP_OFFLINE')=='1')
PY
TOOLS="$CREUSOT_OPTION_WORK/tools/creusot"
PIN=318615be3b8bbc60d1f6d52469ba5c0bdebed4f1
if [[ ! -d "$TOOLS/.git" ]]; then
  mkdir -p "$(dirname "$TOOLS")"
  git clone --no-checkout "${CREUSOT_GIT_CACHE:-https://github.com/creusot-rs/creusot.git}" "$TOOLS"
  git -C "$TOOLS" checkout --detach "$PIN"
fi
[[ "$(git -C "$TOOLS" rev-parse HEAD)" == "$PIN" ]]
[[ -z "$(git -C "$TOOLS" status --porcelain --untracked-files=no)" ]]
if ! rustup run nightly-2026-06-22 rustc --version >/dev/null 2>&1; then
  rustup toolchain install nightly-2026-06-22 --profile minimal --component rustc-dev --component llvm-tools --component rustfmt --component rust-src
fi
if [[ ! -x "$CREUSOT_DATA_HOME/toolchains/nightly-2026-06-22/bin/creusot-rustc" ]]; then
  (cd /private/tmp; cargo build --release --locked --manifest-path "$TOOLS/Cargo.toml" -p cargo-creusot -p creusot-rustc -p prelude-generator)
fi
mkdir -p "$CARGO_HOME/bin" "$CREUSOT_DATA_HOME/bin" "$CREUSOT_DATA_HOME/toolchains/nightly-2026-06-22/bin"
cp "$TOOLS/target/release/cargo-creusot" "$CARGO_HOME/bin/cargo-creusot"
cp "$TOOLS/target/release/creusot-rustc" "$CREUSOT_DATA_HOME/toolchains/nightly-2026-06-22/bin/creusot-rustc"
CARGO_MANIFEST_DIR="$TOOLS/prelude-generator" "$TOOLS/target/release/prelude-generator"
mkdir -p "$CREUSOT_DATA_HOME/share/why3find/packages/creusot/creusot"
cp -R "$TOOLS/target/creusot/packages/creusot/creusot/." "$CREUSOT_DATA_HOME/share/why3find/packages/creusot/creusot/"
ln -sfn "$CREUSOT_OPAM_PREFIX/bin/why3" "$CREUSOT_DATA_HOME/bin/why3"
ln -sfn "$CREUSOT_OPAM_PREFIX/bin/why3find" "$CREUSOT_DATA_HOME/bin/why3find"
ln -sfn "$CREUSOT_PROVER_DIR/z3" "$CREUSOT_DATA_HOME/bin/z3"
cp "$ROOT/verification/why3.conf" "$CREUSOT_DATA_HOME/creusot_why3.conf"
cp "$ROOT/why3find.json" "$CREUSOT_DATA_HOME/why3find.json"
(cd "$ROOT"; cargo fetch --locked)
python3.11 "$ROOT/scripts/check-source.py"
python3.11 "$ROOT/scripts/check-tools.py"
