#!/usr/bin/env bash
set -euo pipefail

: "${AENEAS_RUN_DIR:?Run through scripts/verify.sh to record the extraction probes.}"
: "${AENEAS_EXTRACT_RUST:?Use the pinned Charon Rust toolchain.}"
crate_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
profile="$crate_root/aeneas/profiles/default"
extractor="$crate_root/../../scripts/aeneas-extract.py"
target="$(rustc -vV | sed -n 's/^host: //p')"
lean_project="$crate_root/.work/build/default/$target/proofs"

for config in "$profile"/probes/*.json; do
    name="$(basename "$config" .json)"
    output="$AENEAS_RUN_DIR/probe-$name"
    RUSTUP_TOOLCHAIN="$AENEAS_EXTRACT_RUST" \
        python3.11 "$extractor" "$crate_root" --config "$config" --output "$output"
    (
        cd "$lean_project"
        for model in "$output"/*.lean; do
            lake env lean "$model"
        done
    ) > "$output/lean.log" 2>&1 || { cat "$output/lean.log"; exit 1; }
done
