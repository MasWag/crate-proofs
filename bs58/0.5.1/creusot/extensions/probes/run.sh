#!/usr/bin/env bash
# Diagnostic evidence only; never a product coverage runner.
set -euo pipefail
probe_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
version_dir=$(cd "$probe_dir/../.." && pwd)
source "$version_dir/scripts/env.sh"
run_dir=$(mktemp -d "$version_dir/.work/extensions/probes/run-XXXXXXXX")
printf '%s\n' "$run_dir"
cd "$probe_dir"
sha256sum Cargo.toml Cargo.lock src/*.rs > "$run_dir/inputs-before.sha256"
git -C "$version_dir/.work/tools/sources/creusot" rev-parse HEAD > "$run_dir/tool-revision.txt"
git -C "$version_dir/.work/tools/sources/creusot" status --porcelain > "$run_dir/tool-status.txt"
[[ ! -s "$run_dir/tool-status.txt" ]]
cargo creusot --only=coma --span-mode absolute --output-dir "$run_dir/coma" -- --locked --offline --target-dir "$run_dir/target" > "$run_dir/compile.log" 2>&1
base="$run_dir/coma/verif/bs58_boundary_probes_rlib"
options=(prove --no-cache -f --summary --no-autodetect-provers -P z3,cvc5 -j 2 --fast 0.2 --time 5 -d 4 -H 3 --preprocess compute_specified)
why3find "${options[@]}" "$base"/vec_utils/*.coma "$base/adapted_slice.coma" "$base/display.coma" "$base"/impl_{Clone,Debug,PartialEq}_for_Derived/*.coma > "$run_dir/positive-prove.log" 2>&1
set +e
why3find "${options[@]}" "$base"/{resize,truncate,as_mut_slice,into_bytes,from_utf8,as_bytes_mut,utf8_guard_step,sha_digest,sha_update,string_push_ascii}.coma > "$run_dir/blocked-prove.log" 2>&1
blocked_status=$?
set -e
printf '%s\n' "$blocked_status" > "$run_dir/blocked-prove.exit"
sha256sum Cargo.toml Cargo.lock src/*.rs > "$run_dir/inputs-after.sha256"
cmp "$run_dir/inputs-before.sha256" "$run_dir/inputs-after.sha256"
# Negative probes must remain open; a successful result would require review.
[[ "$blocked_status" -ne 0 ]]
