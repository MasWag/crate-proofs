#!/usr/bin/env bash
# Extract the actual-call absence observers against optimized release metadata.
set -euo pipefail

version_root="$(cd "$1" && pwd)"
observer_root="$(cd "$2" && pwd)"
output_parent="$(cd "$3" && pwd)"
output="$(mktemp -d "$output_parent/error-observers-XXXXXXXX")"
printf '%s\n' "$output"
export RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_NET_OFFLINE=true
export PATH="$version_root/.work/selected-tools/aeneas/bin:$version_root/.work/selected-tools/aeneas/charon/bin:$PATH"
run_logged() {
    printf '%q ' "$@" >>"$output/commands.log"
    printf '\n' >>"$output/commands.log"
    "$@"
}
cd "$version_root"
flags='-Zalways-encode-mir=yes -Zcross-crate-inline-threshold=1000 -Zinline-mir=yes'
run_logged env "RUSTFLAGS=$flags" "CARGO_TARGET_DIR=$output/target" \
    cargo build --release --lib --locked --offline --message-format=json \
    >"$output/build.json" 2>"$output/build.log"
metadata="$(python3.11 - "$output/build.json" "$version_root" <<'PY'
import json
import sys
from pathlib import Path

build = Path(sys.argv[1])
root = Path(sys.argv[2])
metadata = []
for line in build.open():
    event = json.loads(line)
    if event.get("reason") != "compiler-artifact":
        continue
    if Path(event["manifest_path"]) != root / "Cargo.toml":
        continue
    assert Path(event["target"]["src_path"]) == root / ".work/source/src/lib.rs"
    assert set(event["features"]) == {"default", "std"}
    assert event["profile"]["opt_level"] == "3"
    metadata.extend(path for path in event["filenames"] if path.endswith(".rmeta"))
assert len(metadata) == 1
print(metadata[0])
PY
)"
cd "$observer_root"
run_logged charon rustc --preset=aeneas --sysroot default --mir optimized \
    --start-from crate::source_is_none --start-from crate::cause_is_none \
    --opaque crate --include crate::source_is_none --include crate::cause_is_none \
    --include leb128fmt::Error --include leb128fmt::InnerError \
    --include 'leb128fmt::_::source' --include core::error::Error::source \
    --include core::error::Error::cause --remove-unused-clauses \
    --print-ullbc --dest-file "$output/Observer.llbc" -- \
    --crate-name leb128fmt_error_observers --crate-type lib --edition 2021 \
    --extern "leb128fmt=$metadata" -Zinline-mir=yes -Zcross-crate-inline-threshold=1000 \
    -Zinline-mir-threshold=1000 -Zmir-enable-passes=+Inline,+DataflowConstProp,+SimplifyLocals-final \
    -Zdump-mir=is_none "-Zdump-mir-dir=$output/mir" src/lib.rs >"$output/charon.log" 2>&1
run_logged aeneas -backend lean -dest "$output" "$output/Observer.llbc" >"$output/aeneas.log" 2>&1
for name in source cause; do
    matches=("$output"/mir/*."${name}_is_none".*.Inline.after.mir)
    test "${#matches[@]}" -eq 1
    grep -F '(inlined <leb128fmt::Error as std::error::Error>::source)' "${matches[0]}"
    grep -F 'Option::<&dyn std::error::Error>::None' "${matches[0]}"
    if [[ "$name" == cause ]]; then
        grep -F '(inlined <leb128fmt::Error as std::error::Error>::cause)' "${matches[0]}"
    fi
done
shasum -a 256 "$version_root/source.lock.json" "$version_root/.work/source/src/lib.rs" \
    "$observer_root/src/lib.rs" "$metadata" "$output/Observer.llbc" "$output/Observer.lean" \
    >"$output/sha256.txt"
