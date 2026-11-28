#!/usr/bin/env bash
# Replay the known Error formatter and source boundaries after offline setup and verification.
set -euo pipefail

crate_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$crate_root"
lean_project="$crate_root/.work/build/default/aarch64-apple-darwin/proofs"
export PATH="$crate_root/.work/selected-tools/aeneas/bin:$crate_root/.work/selected-tools/aeneas/charon/bin:$PATH"
export RUSTUP_TOOLCHAIN=nightly-2026-09-17
export CARGO_NET_OFFLINE=true
probe_dir="$(mktemp -d "${AENEAS_RUN_DIR:-$crate_root/.work}/error-trait-boundaries-XXXXXXXX")"
printf '%s\n' "$probe_dir"
run_logged() {
    printf '%q ' "$@" >>"$probe_dir/commands.log"
    printf '\n' >>"$probe_dir/commands.log"
    "$@"
}

extract_charon() {
    local directory="$1" method="$2" root="$3"
    shift 3
    mkdir "$directory"
    run_logged charon cargo --preset=aeneas --start-from "$root" --opaque crate \
        --include crate::Error --include crate::InnerError --include "crate::_::$method" \
        --remove-unused-clauses "$@" --dest-file "$directory/Probe.llbc" -- --lib --locked \
        >"$directory/charon.log" 2>&1
}

for trait in Display Debug; do
    directory="$probe_dir/$trait"
    extract_charon "$directory" fmt "{impl core::fmt::$trait for crate::Error}::fmt" \
        --include core::fmt::Formatter \
        --include core::fmt::_::write_str \
        --include core::fmt::_::debug_tuple_field1_finish
    if run_logged aeneas -backend lean -dest "$directory" "$directory/Probe.llbc" \
        >"$directory/aeneas.log" 2>&1; then
        printf 'Unexpected success extracting the real %s formatter\n' "$trait" >&2
        exit 1
    fi
    grep -F 'Dynamic trait types are not supported yet' "$directory/aeneas.log"
    grep -F "Could not translate type decl 'core::fmt::Formatter" "$directory/aeneas.log"
done

directory="$probe_dir/Source"
extract_charon "$directory" source '{impl core::error::Error for crate::Error}::source' \
    --include core::error::Error::source
run_logged aeneas -backend lean -dest "$directory" "$directory/Probe.llbc" >"$directory/aeneas.log" 2>&1
cat >"$directory/AuditSource.lean" <<'LEAN'
import Probe

open Aeneas Aeneas.Std

theorem releaseSourceReturnsNone (error : leb128fmt.Error) :
    leb128fmt.Error.Insts.CoreErrorError.source error = .ok none := by
  rfl

#print axioms releaseSourceReturnsNone
LEAN
lean_path="$(cd "$lean_project" && lake env printenv LEAN_PATH)"
(
    cd "$directory"
    export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
    LEAN_PATH="$lean_path" run_logged lean -o Probe.olean Probe.lean
    LEAN_PATH="$directory:$lean_path" run_logged lean AuditSource.lean >lean-audit.log
)
grep -F 'core.fmt.Formatter' "$directory/lean-audit.log"

directory="$probe_dir/Cause"
mkdir "$directory"
(
    cd "$crate_root/verification/harness/error-defaults"
    run_logged charon cargo --preset=aeneas --start-from crate::cause --opaque crate \
        --include crate::cause --include leb128fmt::Error --include leb128fmt::InnerError \
        --include 'leb128fmt::_::source' --include core::error::Error::source \
        --include core::error::Error::cause --remove-unused-clauses \
        --dest-file "$directory/Probe.llbc" -- --lib --locked
) >"$directory/charon.log" 2>&1
run_logged aeneas -backend lean -dest "$directory" "$directory/Probe.llbc" >"$directory/aeneas.log" 2>&1
if (
    cd "$directory"
    ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 LEAN_PATH="$lean_path" run_logged lean Probe.lean
) >"$directory/lean.log" 2>&1; then
    echo 'Inherited Error::cause now typechecks. Revisit the dynamic error model.' >&2
    exit 1
fi
grep -F 'Invalid field `source`' "$directory/lean.log"
grep -F '`cause` is not a field of structure `core.error.Error`' "$directory/lean.log"
