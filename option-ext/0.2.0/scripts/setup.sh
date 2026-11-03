#!/usr/bin/env bash
set -euo pipefail
CRATE_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$CRATE_ROOT/scripts/env.sh"
if [[ ! -x "$CRATE_ROOT/.work/gnu-make/bin/make" ]]; then
  bash "$CRATE_ROOT/scripts/bootstrap-make.sh"
fi
"$OPTION_EXT_PYTHON" "$CRATE_ROOT/../../scripts/aeneas-manage.py" setup "$CRATE_ROOT" --sources-only
"$OPTION_EXT_PYTHON" "$CRATE_ROOT/scripts/check-adaptation.py" --prepare
export PATH="$CRATE_ROOT/scripts/build-tools:$PATH"
# This host has the libraries already installed; opam's Homebrew detector does
# not recognize them. Skip only that detector when both real inputs are present.
if [[ -f /opt/homebrew/opt/gmp/include/gmp.h && -x /opt/homebrew/opt/pkgconf/bin/pkgconf ]]; then
  export OPAMASSUMEDEPEXTS=true
fi
exec "$OPTION_EXT_PYTHON" "$CRATE_ROOT/../../scripts/aeneas-manage.py" setup "$CRATE_ROOT" "$@"
