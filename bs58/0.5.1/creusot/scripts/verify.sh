#!/usr/bin/env bash
# Fresh, cache-disabled proof attempt for every emitted target in the standalone
# bs58 Creusot crate. A failed attempt remains in .work for inspection.
set -euo pipefail
version_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
env_root="$version_dir/.work/tools"
source "$env_root/env.sh"
export RUSTUP_TOOLCHAIN=nightly-2026-06-22
export CARGO_NET_OFFLINE=true
crate_dir="$version_dir/crate"
mkdir -p "$version_dir/.work"
run_dir=$(mktemp -d "$version_dir/.work/creusot-run-XXXXXXXX")
export CARGO_TARGET_DIR="$run_dir/target"
export TMPDIR="$run_dir/tmp"
export XDG_CACHE_HOME="$run_dir/cache"
mkdir -p "$TMPDIR" "$XDG_CACHE_HOME"
printf 'Fresh run: %s\n' "$run_dir"

hash_inputs() {
    local files=(
        "$version_dir/AGENTS.md"
        "$version_dir/correspondence.md"
        "$version_dir/verification/specification.md"
        "$version_dir/verification/release-identity.json"
        "$version_dir/verification/toolchain.json"
        "$version_dir/../source.lock.json"
        "$version_dir/scripts/verify.sh"
        "$version_dir/scripts/check-run.py"
        "$crate_dir/Cargo.toml"
        "$crate_dir/Cargo.lock"
        "$version_dir/../../../why3find.json"
        "$env_root/env.sh"
        "$XDG_DATA_HOME/creusot/creusot_why3.conf"
        "$XDG_DATA_HOME/creusot/why3find.json"
    )
    mapfile -t sources < <(rg --files --no-ignore "$crate_dir/src" | sort)
    files+=("${sources[@]}")
    mapfile -t prelude < <(rg --files --no-ignore "$XDG_DATA_HOME/creusot/share/why3find/packages/creusot" | sort)
    files+=("${prelude[@]}")
    if [[ -f "$version_dir/scripts/setup-tools.sh" ]]; then
        files+=("$version_dir/scripts/setup-tools.sh")
    fi
    files+=("$XDG_DATA_HOME/creusot/toolchains/nightly-2026-06-22/bin/creusot-rustc")
    files+=("$(rustup which rustc --toolchain nightly-2026-06-22)")
    local drivers=()
    for candidate in "$RUSTUP_HOME"/toolchains/nightly-2026-06-22-x86_64-unknown-linux-gnu/lib/librustc_driver-*.so; do
        if [[ -f "$candidate" ]]; then
            drivers+=("$candidate")
        fi
    done
    [[ "${#drivers[@]}" -eq 1 ]] || {
        printf 'Expected exactly one pinned rustc driver library.\n' >&2
        return 1
    }
    files+=("${drivers[@]}")
    local config_dir="$crate_dir"
    while :; do
        for config_name in config config.toml; do
            if [[ -f "$config_dir/.cargo/$config_name" ]]; then
                files+=("$config_dir/.cargo/$config_name")
            fi
        done
        [[ "$config_dir" == / ]] && break
        config_dir=$(dirname "$config_dir")
    done
    for config_name in config config.toml; do
        if [[ -f "$CARGO_HOME/$config_name" ]]; then
            files+=("$CARGO_HOME/$config_name")
        fi
    done
    for binary in cargo-creusot why3find why3 z3 cvc5; do
        local path
        path=$(command -v "$binary")
        files+=("$path")
    done
    sha256sum "${files[@]}"
    python3 - <<'PY'
import hashlib
import os

names = sorted(name for name in os.environ if name in {
    'RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'RUSTC', 'RUSTC_WRAPPER',
    'RUSTC_WORKSPACE_WRAPPER', 'CARGO_BUILD_RUSTC', 'CARGO_BUILD_RUSTFLAGS',
    'RUSTUP_TOOLCHAIN', 'CARGO_HOME', 'RUSTUP_HOME', 'CARGO_TARGET_DIR',
} or name.startswith('CARGO_PROFILE_'))
for name in names:
    digest = hashlib.sha256(os.environ[name].encode()).hexdigest()
    print(f'{digest}  env:{name}')
PY
}

check_tool_source() {
    local checkout="$env_root/sources/creusot"
    local expected=318615be3b8bbc60d1f6d52469ba5c0bdebed4f1
    local actual
    actual=$(git -C "$checkout" rev-parse HEAD)
    [[ "$actual" == "$expected" ]] || {
        printf 'Unexpected Creusot source revision: %s\n' "$actual" >&2
        return 1
    }
    [[ -z "$(git -C "$checkout" status --porcelain)" ]] || {
        printf 'Creusot source checkout is dirty.\n' >&2
        return 1
    }
}

check_tool_source
python3 - "$version_dir/verification/toolchain.json" "$RUSTUP_HOME" <<'PY'
import hashlib
import json
import pathlib
import sys

expected = json.loads(pathlib.Path(sys.argv[1]).read_text())['rustc_driver']
if len(expected) != 1:
    raise SystemExit('Toolchain manifest must identify exactly one rustc driver')
path, digest = next(iter(expected.items()))
driver = pathlib.Path(path)
if not driver.is_file() or not driver.resolve().is_relative_to(pathlib.Path(sys.argv[2]).resolve()):
    raise SystemExit('Pinned rustc driver path is missing or outside RUSTUP_HOME')
if hashlib.sha256(driver.read_bytes()).hexdigest() != digest:
    raise SystemExit('Pinned rustc driver digest differs from toolchain manifest')
PY
[[ "$(realpath "$crate_dir/../.work/tools/sources/creusot/creusot-std")" == \
   "$(realpath "$env_root/sources/creusot/creusot-std")" ]] || {
    printf 'creusot-std dependency does not resolve to the pinned source checkout.\n' >&2
    exit 1
}
hash_inputs > "$run_dir/inputs-before.sha256"
{
    cargo creusot version
    rustc --version --verbose
    why3 --version
    why3find --version
    z3 --version
    cvc5 --version
    git -C "$env_root/sources/creusot" rev-parse HEAD
} > "$run_dir/versions.txt" 2>&1

cd "$crate_dir"
set +e
cargo creusot --only=coma --span-mode absolute --output-dir "$run_dir/coma" -- \
    --locked --offline --target-dir "$run_dir/target" > "$run_dir/compile.log" 2>&1
compile_status=$?
set -e
printf '%s\n' "$compile_status" > "$run_dir/compile.exit"
if [[ "$compile_status" -ne 0 ]]; then
    check_tool_source
    hash_inputs > "$run_dir/inputs-after.sha256"
    printf 'Translation failed; see %s/compile.log\n' "$run_dir" >&2
    exit 1
fi

mapfile -t targets < <(rg --files --no-ignore "$run_dir/coma" | rg '\.coma$' | sort)
printf '%s\n' "${targets[@]}" > "$run_dir/generated-targets.txt"
if [[ "${#targets[@]}" -eq 0 ]]; then
    printf 'Translation emitted zero Coma targets.\n' >&2
    exit 1
fi
for required in impl_Alphabet/new encode_into decode_into decode_into_const; do
    if [[ ! -f "$run_dir/coma/verif/bs58_creusot_rlib/$required.coma" ]]; then
        printf 'Missing core target: %s\n' "$required" >&2
        exit 1
    fi
done

: > "$run_dir/prove.log"
: > "$run_dir/target-exits.tsv"
prove_status=0
for target in "${targets[@]}"; do
    target_rel=${target#"$run_dir/coma/"}
    target_log="$run_dir/prover-logs/${target_rel%.coma}.log"
    mkdir -p "$(dirname "$target_log")"
    if why3find prove --no-cache -f --summary --no-autodetect-provers \
        -P z3,cvc5 -j 2 --fast 0.2 --time 5 -d 4 -H 3 \
        --preprocess compute_specified "$target" > "$target_log" 2>&1; then
        target_status=0
    else
        target_status=$?
        prove_status=1
    fi
    printf '%s\t%s\n' "$target" "$target_status" >> "$run_dir/target-exits.tsv"
    printf '[%s] exit=%s\n' "$target_rel" "$target_status" >> "$run_dir/prove.log"
    cat "$target_log" >> "$run_dir/prove.log"
done
printf '%s\n' "$prove_status" > "$run_dir/prove.exit"
check_tool_source
hash_inputs > "$run_dir/inputs-after.sha256"
if ! cmp -s "$run_dir/inputs-before.sha256" "$run_dir/inputs-after.sha256"; then
    printf 'Fingerprint mismatch during proof; see %s\n' "$run_dir" >&2
    exit 1
fi
python3 "$version_dir/scripts/check-run.py" "$run_dir"
if [[ "$prove_status" -ne 0 ]]; then
    printf 'One or more proof goals are open; see %s/prove.log\n' "$run_dir" >&2
    exit 1
fi
printf 'All generated goal trees closed: %s\n' "$run_dir"
