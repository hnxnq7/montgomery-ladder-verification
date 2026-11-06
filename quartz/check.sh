#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
bash quartz/setup.sh
export OCAMLPATH="$PWD/.deps/quartz/_build/install/default/lib${OCAMLPATH:+:$OCAMLPATH}"
for module in field_words memory processor_tests accelerator accelerator_tests \
    accelerator_cpu accelerator_cpu_tests; do
  rocq compile -Q .deps/quartz/_build/default/lang quartz.lang \
    -Q .deps/quartz/_build/default/examples quartz.examples \
    -Q quartz LadderQuartz "quartz/$module.v"
done
