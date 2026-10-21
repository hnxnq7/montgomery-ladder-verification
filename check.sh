#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

for module in ladder_math dual_circuit ladder_machine ladder_machine_tests state_machine state_machine_tests two_reg_prob montgomery_ladder; do
  printf 'Checking %s.v\n' "$module"
  coqc -Q . "" "$module.v"
done
bash setup_fiat_crypto.sh
for module in curve25519 curve25519_tests; do
  printf 'Checking %s.v\n' "$module"
  coqc -Q . "" -R .deps/fiat-crypto/src Crypto \
    -Q .deps/fiat-crypto/rewriter/src/Rewriter Rewriter \
    -R .deps/fiat-crypto/coqprime/src/Coqprime Coqprime "$module.v"
done
printf 'Build passed. This accepts any remaining Admitted declarations.\n'
