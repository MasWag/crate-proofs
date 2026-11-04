#!/usr/bin/env bash
set -euo pipefail
extension_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
source "$extension_root/../scripts/env.sh"
exec python3 "$extension_root/scripts/verify.py" "$@"
