#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

for file in finite_masking word_masking shared_ladder ladder_distribution tests; do
  rocq compile -q -w -notation-overridden,-ambiguous-paths -Q masking Masking "masking/$file.v"
done
