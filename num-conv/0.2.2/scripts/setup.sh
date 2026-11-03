#!/usr/bin/env bash
set -euo pipefail
CRATE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$CRATE_ROOT/scripts/env.sh"
exec "$PYTHON3" "$CRATE_ROOT/../../scripts/aeneas-manage.py" setup "$CRATE_ROOT" "$@"
