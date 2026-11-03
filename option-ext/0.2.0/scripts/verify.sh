#!/usr/bin/env bash
set -euo pipefail
CRATE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$CRATE_ROOT/scripts/env.sh"
"$OPTION_EXT_PYTHON" "$CRATE_ROOT/scripts/check-adaptation.py" --prepare
exec "$OPTION_EXT_PYTHON" "$CRATE_ROOT/../../scripts/aeneas-manage.py" verify "$CRATE_ROOT" "$@"
