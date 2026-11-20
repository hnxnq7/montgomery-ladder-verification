#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
root="$PWD"
build="$root/.deps/quartz-math"
for command in rocq coqc coqtop coq_makefile; do
  if ! command -v "$command" >/dev/null 2>&1; then
    printf 'Missing %s; install coq-core.9.1.0 in the Quartz switch.\n' "$command" >&2
    exit 1
  fi
done
if [[ "$(coqc -where)" != "$(rocq compile -where)" || "$(coqtop -where)" != "$(rocq compile -where)" ]]; then
  printf 'Rocq and Coq compatibility commands must use the same Quartz switch.\n' >&2
  exit 1
fi
mkdir -p "$build"

# Keep the Quartz toolchain's curve artifacts separate from the root build.
cp ladder_math.v curve25519_math.v setup_fiat_crypto.sh "$build/"
bash "$build/setup_fiat_crypto.sh"
cd "$build"
rocq compile -Q . "" ladder_math.v
rocq compile -Q . "" -R .deps/fiat-crypto/src Crypto \
  -Q .deps/fiat-crypto/rewriter/src/Rewriter Rewriter \
  -R .deps/fiat-crypto/coqprime/src/Coqprime Coqprime curve25519_math.v
