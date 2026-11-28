#!/usr/bin/env bash
set -euo pipefail

: "${AENEAS_RUN_DIR:?Run through scripts/verify.sh to record native observations.}"
crate_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
output="$AENEAS_RUN_DIR/native-observations"
mkdir "$output"

for profile in debug release; do
    rust_flags=(-C overflow-checks=on)
    if [[ "$profile" == release ]]; then
        rust_flags=(-O -C overflow-checks=off)
    fi
    library="$output/libleb128fmt-$profile.rlib"
    rustc --edition=2021 --crate-name leb128fmt --crate-type rlib \
        "${rust_flags[@]}" "$crate_root/.work/source/src/lib.rs" -o "$library"
    for observation in "$crate_root"/verification/*_observations.rs; do
        name="$(basename "$observation" .rs)"
        executable="$output/$name-$profile"
        rustc --edition=2021 --test "${rust_flags[@]}" "$observation" \
            --extern "leb128fmt=$library" -o "$executable"
        "$executable"
    done
done
