#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
bash quartz/setup.sh
root="$PWD"
dune build --root "$root/.deps/quartz" lang/sv.vo
export OCAMLPATH="$PWD/.deps/quartz/_build/install/default/lib${OCAMLPATH:+:$OCAMLPATH}"
for module in field_words memory processor_tests accelerator accelerator_tests \
    accelerator_correctness accelerator_correctness_tests accelerator_leakage hamming_weight packed_storage protected_accelerator \
    accelerator_cpu accelerator_cpu_tests; do
  rocq compile -Q .deps/quartz/_build/default/lang quartz.lang \
    -Q .deps/quartz/_build/default/examples quartz.examples \
    -Q quartz LadderQuartz "quartz/$module.v"
done

# Compile shared curve theory under Quartz's Stdlib without replacing root artifacts.
bash "$root/quartz/setup_math.sh"
cd "$root/.deps/quartz-math"
paths=(-Q . "" -Q "$root/.deps/quartz/_build/default/lang" quartz.lang
  -Q "$root/.deps/quartz/_build/default/examples" quartz.examples -Q "$root/quartz" LadderQuartz
  -R .deps/fiat-crypto/src Crypto -Q .deps/fiat-crypto/rewriter/src/Rewriter Rewriter
  -R .deps/fiat-crypto/coqprime/src/Coqprime Coqprime)
rocq compile "${paths[@]}" "$root/quartz/accelerator_ladder_bridge.v"
rocq compile "${paths[@]}" "$root/quartz/ladder_controller.v"
rocq compile "${paths[@]}" "$root/quartz/controller_protection.v"
rocq compile "${paths[@]}" "$root/quartz/controller_rtl_export.v"
rocq compile "${paths[@]}" "$root/quartz/protected_accelerator_security.v"
rocq compile "${paths[@]}" "$root/quartz/accelerator_cpu_security.v"
rocq compile "${paths[@]}" "$root/quartz/protected_accelerator_tests.v"
rocqchk -silent "${paths[@]}" LadderQuartz.accelerator_ladder_bridge \
  LadderQuartz.accelerator_correctness_tests LadderQuartz.accelerator_leakage \
  LadderQuartz.protected_accelerator_tests LadderQuartz.accelerator_cpu_security \
  LadderQuartz.ladder_controller LadderQuartz.controller_protection LadderQuartz.controller_rtl_export
echo "Quartz build and kernel check passed."
