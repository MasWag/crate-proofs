#!/usr/bin/env bash
set -euo pipefail
behavior_dir="$(cd "$(dirname "$0")" && pwd)"
version_dir="$(cd "$behavior_dir/../.." && pwd)"
export CARGO_HOME="$version_dir/.work/cargo-home"
export CARGO_TARGET_DIR="$version_dir/.work/behavior/target"
mkdir -p "$version_dir/.work/behavior"
# Cargo discovers ancestor configuration from cwd even with --manifest-path.
cd /private/tmp
base=(rustup run 1.94.1 cargo test --locked --offline --manifest-path "$behavior_dir/Cargo.toml")
"${base[@]}" -- --nocapture > "$version_dir/.work/behavior/controls.log" 2>&1
set +e
"${base[@]}" -- --ignored --nocapture > "$version_dir/.work/behavior/regressions.log" 2>&1
regressions_status=$?
set -e
printf 'Controls passed; expected-correct regression assertions exited %s (expected 101).\n' "$regressions_status"
test "$regressions_status" -eq 101
