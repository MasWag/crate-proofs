#!/usr/bin/env bash
set -euo pipefail

: "${AENEAS_RUN_DIR:?Run through scripts/verify.sh to record the conversion probe.}"
: "${AENEAS_PROOF_DIR:?Run through scripts/verify.sh for the pinned Lean environment.}"
crate_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
probe_conversions() {
    local output="$1"
    shift
    bash "$crate_root/scripts/extract-slice-instantiations.sh" all "$output" "$@"
    if (cd "$AENEAS_PROOF_DIR" && lake env lean "$output/SliceConcrete.lean") >"$output/lean.log" 2>&1; then
        echo 'All concrete writer dictionaries now typecheck. Revisit the conversion boundary.' >&2
        exit 1
    fi
    grep -F 'error: Application type mismatch' "$output/lean.log"
    grep -F 'core.num.error.IntErrorKind.PosOverflow' "$output/lean.log"
    grep -F 'core.num.error.IntErrorKind.NegOverflow' "$output/lean.log"
    grep -F 'core.num.error.TryFromIntError' "$output/lean.log"
}

probe_conversions "$AENEAS_RUN_DIR/probe-slice-conversions"
probe_conversions "$AENEAS_RUN_DIR/probe-slice-conversions-optimized" optimized
