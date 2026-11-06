#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
build="$root/.deps/masking-curve"
mkdir -p "$build"

# Keep artifacts from the two Stdlib versions separate.
cp ladder_math.v curve25519_math.v setup_fiat_crypto.sh "$build/"
bash "$build/setup_fiat_crypto.sh"
cd "$build"
rocq compile -Q "$build" "" "$build/ladder_math.v"
rocq compile -Q "$build" "" -R "$build/.deps/fiat-crypto/src" Crypto \
  -Q "$build/.deps/fiat-crypto/rewriter/src/Rewriter" Rewriter \
  -R "$build/.deps/fiat-crypto/coqprime/src/Coqprime" Coqprime "$build/curve25519_math.v"
