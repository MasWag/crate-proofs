#!/usr/bin/env bash
set -euo pipefail

: "${AENEAS_RUN_DIR:?Run through scripts/verify.sh.}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
target="$(rustc -vV | sed -n 's/^host: //p')"
log="$AENEAS_RUN_DIR/error-observers-replay.log"
bash "$root/scripts/replay-error-observers.sh" "$root" \
    "$root/verification/harness/error-observers" "$AENEAS_RUN_DIR" >"$log"
IFS= read -r probe <"$log"
cmp "$probe/Observer.lean" \
    "$root/aeneas/profiles/default/proofs/Generated/$target/Observer.lean"
