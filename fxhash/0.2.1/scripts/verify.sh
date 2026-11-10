#!/usr/bin/env bash
set -euo pipefail
CRATE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$CRATE_ROOT/scripts/env.sh"
exec python3.11 "$CRATE_ROOT/../../scripts/aeneas-manage.py" verify "$CRATE_ROOT" "$@"
