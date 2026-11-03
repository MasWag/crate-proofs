#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
python3 "$ROOT/scripts/prepare.py" --check
export CARGO_NET_OFFLINE=true
cargo kani --manifest-path "$ROOT/Cargo.toml" -Z function-contracts "$@"
