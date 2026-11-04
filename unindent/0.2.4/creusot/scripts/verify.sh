#!/usr/bin/env bash
set -euo pipefail
UNINDENT_CREUSOT_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
UNINDENT_REPO_ROOT="$(cd -- "$UNINDENT_CREUSOT_ROOT/../../.." && pwd)"
cd "$UNINDENT_CREUSOT_ROOT"
source scripts/env.sh
mkdir -p .work/runs
UNINDENT_RUN=$(mktemp -d "$UNINDENT_CREUSOT_ROOT/.work/runs/creusot-XXXXXXXX")
mkdir -p "$UNINDENT_RUN/coma"
printf 'Fresh Creusot evidence: %s\n' "$UNINDENT_RUN"
{ cargo creusot version; rustc -Vv; why3find --version; why3 --version; z3 --version; cvc5 --version; alt-ergo --version; } > "$UNINDENT_RUN/versions.txt" 2>&1
python3 scripts/check-proofs.py snapshot "$UNINDENT_RUN/inputs-before.json"
set +e
cargo test --locked --offline --target-dir "$UNINDENT_RUN/native-target" -- --nocapture > "$UNINDENT_RUN/native.log" 2>&1
UNINDENT_NATIVE_EXIT=$?
set -e
printf '%s\n' "$UNINDENT_NATIVE_EXIT" > "$UNINDENT_RUN/native.exit"
[[ "$UNINDENT_NATIVE_EXIT" == 0 ]] || { tail -40 "$UNINDENT_RUN/native.log"; exit "$UNINDENT_NATIVE_EXIT"; }
cargo creusot --only=coma --span-mode absolute --output-dir "$UNINDENT_RUN/coma" -- --locked --offline --target-dir "$UNINDENT_RUN/proof-target" > "$UNINDENT_RUN/compile.log" 2>&1
mapfile -t UNINDENT_TARGETS < <(python3 scripts/check-proofs.py selected "$UNINDENT_RUN")
[[ ${#UNINDENT_TARGETS[@]} -gt 0 ]] || { echo 'No reviewed positive targets' >&2; exit 1; }
set +e
why3find prove --no-cache -f --summary --no-autodetect-provers -P z3,cvc5,alt-ergo -j 2 --fast 1 --time 10 -d 6 "${UNINDENT_TARGETS[@]}" > "$UNINDENT_RUN/prove.log" 2>&1
UNINDENT_PROVE_EXIT=$?
set -e
printf '%s\n' "$UNINDENT_PROVE_EXIT" > "$UNINDENT_RUN/prove.exit"
[[ "$UNINDENT_PROVE_EXIT" == 0 ]] || { tail -50 "$UNINDENT_RUN/prove.log"; exit "$UNINDENT_PROVE_EXIT"; }
python3 scripts/check-proofs.py package "$UNINDENT_RUN"
python3 "$UNINDENT_REPO_ROOT/scripts/audit-proof-evidence.py" "$UNINDENT_CREUSOT_ROOT" --manifest "$UNINDENT_RUN/bundle/manifest.json" --source-root "$UNINDENT_CREUSOT_ROOT/src" --generated-dir "$UNINDENT_RUN/coma/verif/unindent_rlib" --reconstruct-root-goals > "$UNINDENT_RUN/bundle/audit.json"
printf 'Accepted local bundle: %s\n' "$UNINDENT_RUN/bundle"
