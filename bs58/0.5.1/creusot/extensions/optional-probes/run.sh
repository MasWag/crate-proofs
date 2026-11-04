#!/usr/bin/env bash
# Compile-only diagnostics, outside product verification inputs.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
source ../../scripts/env.sh
out="$PWD/../../.work/extensions/optional-probes"
mkdir -p "$out"
sha256sum Cargo.toml Cargo.lock src/lib.rs > "$out/inputs.sha256"
git -C ../../.work/tools/sources/creusot rev-parse HEAD > "$out/tool-revision.txt"
cargo creusot --only=coma --span-mode absolute --output-dir "$out/coma" -- --locked --offline --target-dir "$out/target" > "$out/compile.log" 2>&1
rg -n 'false' "$out"/coma/verif/bs58_optional_boundary_probes_rlib/*.coma > "$out/false-preconditions.txt"
