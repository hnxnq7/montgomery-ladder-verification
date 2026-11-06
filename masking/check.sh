#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

root="$PWD"
for file in finite_masking word_masking shared_ladder ladder_distribution shared_power shared_loop tests; do
  rocq compile -q -w -notation-overridden,-ambiguous-paths -Q masking Masking "masking/$file.v"
done

bash masking/setup_curve.sh
cd "$root/.deps/masking-curve"
paths=(-Q . "" -Q "$root/masking" Masking
  -R .deps/fiat-crypto/src Crypto
  -Q .deps/fiat-crypto/rewriter/src/Rewriter Rewriter
  -R .deps/fiat-crypto/coqprime/src/Coqprime Coqprime)
for file in fiat_field ladder_bridge masked_curve25519 curve_tests; do
  rocq compile -q -w -notation-overridden,-ambiguous-paths "${paths[@]}" "$root/masking/$file.v"
done
rocqchk -silent "${paths[@]}" Masking.masked_curve25519 Masking.curve_tests
echo "Masking build and kernel check passed."
