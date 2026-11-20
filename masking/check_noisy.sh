#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

for file in dyadic_phase cube_spectral cube_roots cube_bound cube_strong_bound cube_encoding cube_field_bound \
    finite_masking word_masking shared_ladder arithmetic_shares arithmetic_control arithmetic_ladder \
    field_refresh field_mul_gadget \
    trace_masking leakage_counterexamples aggregate_hw_limit noisy_leakage \
    noisy_bit_example xor_shares noisy_shares noisy_channel_bridge noisy_words noisy_trace noisy_history_budget history_semantics \
    arithmetic_privacy arithmetic_refresh arithmetic_aggregate arithmetic_spectral cyclic_characters \
    field_coefficient curve_coefficient \
    noisy_common_mass arithmetic_noisy_snapshot arithmetic_channel arithmetic_bank_refresh arithmetic_product_bound \
    field_history field_mul_leakage field_linear_gadget field_mul_tests field_leakage_tests \
    field_trace_bound field_mul_attack_tests history_semantics_tests noisy_tests; do
  rocq compile -q -w -notation-overridden,-ambiguous-paths -Q masking Masking "masking/$file.v"
done
rocqchk -silent -Q masking Masking \
  Masking.dyadic_phase Masking.cube_spectral Masking.cube_roots Masking.cube_bound \
  Masking.cube_encoding Masking.cube_field_bound \
  Masking.cube_strong_bound Masking.arithmetic_bank_refresh Masking.arithmetic_product_bound \
  Masking.aggregate_hw_limit Masking.noisy_leakage Masking.noisy_trace Masking.noisy_tests \
  Masking.field_history Masking.field_mul_leakage Masking.field_linear_gadget \
  Masking.field_mul_tests Masking.field_leakage_tests Masking.field_trace_bound Masking.noisy_history_budget \
  Masking.field_mul_attack_tests Masking.arithmetic_privacy Masking.arithmetic_shares \
  Masking.arithmetic_refresh Masking.arithmetic_control Masking.arithmetic_ladder \
  Masking.noisy_common_mass Masking.arithmetic_noisy_snapshot Masking.arithmetic_channel \
  Masking.arithmetic_aggregate Masking.arithmetic_spectral Masking.cyclic_characters \
  Masking.field_coefficient Masking.curve_coefficient Masking.history_semantics_tests
echo "Noisy leakage build and kernel check passed."
