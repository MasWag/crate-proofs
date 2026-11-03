#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORK="$ROOT/.work"
ARCHIVE="$WORK/make-4.4.1.tar.gz"
EXPECTED=dd16fb1d67bfab79a72f5e8390735c49e3e8e70b4945a15ab1f81ddb78658fb3
mkdir -p "$WORK"
if [[ ! -f "$ARCHIVE" ]]; then
  curl -fL https://ftp.gnu.org/gnu/make/make-4.4.1.tar.gz -o "$ARCHIVE"
fi
ACTUAL="$(shasum -a 256 "$ARCHIVE" | cut -d ' ' -f 1)"
[[ "$ACTUAL" == "$EXPECTED" ]]
if [[ ! -d "$WORK/make-4.4.1" ]]; then
  tar -xzf "$ARCHIVE" -C "$WORK"
fi
cd "$WORK/make-4.4.1"
./configure --prefix="$WORK/gnu-make"
/usr/bin/make -j8
/usr/bin/make install
