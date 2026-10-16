#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

for module in ladder_math dual_circuit state_machine two_reg_prob montgomery_ladder; do
  printf 'Checking %s.v\n' "$module"
  coqc -Q . "" "$module.v"
done
printf 'Build passed. The seven original admissions remain; this is not a proof audit.\n'
