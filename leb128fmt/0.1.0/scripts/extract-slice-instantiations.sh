#!/usr/bin/env bash
set -euo pipefail

crate_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ $# != 2 && $# != 3 ]]; then
    echo "Usage: $0 {supported|all} NEW_OUTPUT_DIRECTORY [optimized]" >&2
    exit 2
fi
selection="$1"
mkdir "$2"
output="$(cd "$2" && pwd)"
cd "$crate_root/verification/slice-instantiations"

args=()
if [[ ${3:-} == optimized ]]; then
    args+=(--mir optimized)
elif [[ $# == 3 ]]; then
    echo "Unknown MIR selection: $3" >&2
    exit 2
fi
case "$selection" in
    supported)
        args+=(--start-from crate::u8_writer --start-from crate::u8_fixed)
        for type in u8 u16 u32 u64 u128 i16 i32 i64 i128; do
            args+=(--start-from "crate::${type}_reader")
        done
        ;;
    all)
        args+=(--start-from crate)
        ;;
    *)
        echo "Unknown selection: $selection" >&2
        exit 2
        ;;
esac

for symbol in encode_uint_slice encode_fixed_uint_slice decode_uint_slice \
    decode_sint_slice UInt SInt private::Sealed max_len is_last Error InnerError; do
    args+=(--include "leb128fmt::$symbol")
done
if [[ "$selection" == all ]]; then
    args+=(--include leb128fmt::encode_sint_slice --include leb128fmt::encode_fixed_sint_slice)
fi
for trait in UInt SInt; do
    args+=(--include "leb128fmt::{impl leb128fmt::$trait for _}::BITS")
done
for binding in BitAnd:bitand Shr:shr Shl:shl BitOrAssign:bitor_assign ShrAssign:shr_assign; do
    args+=(--include "core::ops::bit::{impl core::ops::bit::${binding%:*}<_> for _}::${binding#*:}")
done
args+=(--include 'core::convert::{impl core::convert::TryFrom<_> for _}::try_from'
       --include 'core::convert::num::{impl core::convert::From<_> for _}::from')
if [[ "$selection" == all ]]; then
    args+=(--include 'core::convert::num::{impl core::convert::TryFrom<_> for _}::try_from'
           --include 'core::num::error::TryFromIntError')
fi

export RUSTUP_TOOLCHAIN="${AENEAS_EXTRACT_RUST:-nightly-2026-09-17}"
export CARGO_ENCODED_RUSTFLAGS="--remap-path-prefix=$crate_root=leb128fmt-0.1.0"
(
    set -x
    charon cargo --preset=aeneas --sysroot default "${args[@]}" --remove-unused-clauses \
        --dest-file "$output/SliceConcrete.llbc" -- --lib --locked
) > "$output/charon.log" 2>&1
(
    set -x
    aeneas -backend lean -dest "$output" "$output/SliceConcrete.llbc"
) > "$output/aeneas.log" 2>&1
if rg -n '^\s*(axiom|opaque|partial\s+def)\b|\b(sorry|admit)\b' "$output/SliceConcrete.lean"; then
    echo "Unsupported or incomplete generated Lean" >&2
    exit 1
fi
