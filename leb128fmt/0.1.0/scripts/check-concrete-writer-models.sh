#!/usr/bin/env bash
set -euo pipefail

: "${AENEAS_RUN_DIR:?Run through scripts/verify.sh.}"
: "${AENEAS_EXTRACT_RUST:?Run through scripts/verify.sh with the pinned compiler.}"
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
target="$(rustc -vV | sed -n 's/^host: //p')"
maintained="$root/aeneas/profiles/default/proofs/Generated/$target"
output="$AENEAS_RUN_DIR/concrete-writer-models"
mkdir "$output"
export RUSTUP_TOOLCHAIN="$AENEAS_EXTRACT_RUST"

roots=()
for ty in u8 u16 u32 u64 u128 i8 i16 i32 i64 i128; do
    roots+=(--start-from "crate::${ty}_writer" --start-from "crate::${ty}_fixed")
done
dependencies=()
for name in encode_uint_slice encode_fixed_uint_slice encode_sint_slice \
    encode_fixed_sint_slice UInt SInt private::Sealed _::BITS; do
    dependencies+=(--include "leb128fmt::$name")
done
for name in bitand shr shr_assign; do
    dependencies+=(--include "core::ops::bit::_::$name")
done

(
    set -x
    cd "$root/verification/slice-instantiations"
    charon cargo --preset=aeneas --sysroot default "${roots[@]}" "${dependencies[@]}" \
        --opaque leb128fmt::max_len --include 'core::convert::_::try_from' \
        --include 'core::convert::num::_::try_from' --include 'core::convert::num::_::from' \
        --include core::num::error::TryFromIntError --remove-unused-clauses \
        --dest-file "$output/ConcreteWriters.llbc" -- --lib --locked
) >"$output/charon.log" 2>&1
(
    set -x
    aeneas -backend lean -split-files -namespace leb128fmt_writer_model -no-progress-bar \
        -dest "$output" "$output/ConcreteWriters.llbc"
) >"$output/aeneas.log" 2>&1

(
    set -x
    cd "$root"
    charon cargo --preset=aeneas --start-from crate::max_len --opaque crate \
        --include crate::max_len --remove-unused-clauses \
        --dest-file "$output/WriterMaxLen.llbc" -- --lib --locked
) >"$output/charon-max-len.log" 2>&1
(
    set -x
    aeneas -backend lean -namespace leb128fmt_writer_max_len -no-progress-bar \
        -dest "$output" "$output/WriterMaxLen.llbc"
) >"$output/aeneas-max-len.log" 2>&1

# The generated template is evidence of the external interface. Lake uses the
# authored module that imports the separately extracted release body.
test "$(sed -n 's/^axiom \([^ ]*\).*/\1/p' "$output/FunsExternal_Template.lean")" = leb128fmt.max_len
cmp "$output/Types.lean" "$maintained/ConcreteWriters/Types.lean"
cmp "$output/Funs.lean" "$maintained/ConcreteWriters/Funs.lean"
cmp "$output/WriterMaxLen.lean" "$maintained/WriterMaxLen.lean"
