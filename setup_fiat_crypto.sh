#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

revision=9d0682462646bf645cba7409fa45794dee0418aa
dependency="$PWD/.deps/fiat-crypto"
jobs="${JOBS:-2}"
mkdir -p .deps

if [[ ! -d "$dependency" ]]; then
  git clone --depth 1 --branch v0.1.6 https://github.com/mit-plv/fiat-crypto.git "$dependency"
fi
if [[ "$(git -C "$dependency" rev-parse HEAD)" != "$revision" ]]; then
  printf 'Fiat-Crypto must be at %s; existing checkout left unchanged.\n' "$revision" >&2
  exit 1
fi
if ! git -C "$dependency" diff --quiet HEAD -- src; then
  printf 'Fiat-Crypto has local source changes; please review them before building.\n' >&2
  exit 1
fi

git -C "$dependency" submodule update --init --depth 1 coqprime rewriter
cd -- "$dependency"
printf 'Checking Fiat-Crypto v0.1.6 (first build takes a few minutes)\n'

if ! make -C coqprime -j"$jobs" COQEXTRAFLAGS='-w -all' \
    src/Coqprime/PrimalityTest/Zp.vo src/Coqprime/PrimalityTest/PocklingtonCertificat.vo \
    > ../coqprime-build.log 2>&1; then
  tail -n 60 ../coqprime-build.log >&2
  exit 1
fi

# Build only the dependency closure of the curve theory, not code generation or CPUs.
sources=()
while IFS= read -r source; do
  sources+=("$source")
done < <(find src/Algebra src/Util src/Spec src/Curves src/Arithmetic \
  rewriter/src/Rewriter/Util -name '*.v' -type f)

coq_makefile -R src Crypto -Q rewriter/src/Rewriter Rewriter \
  -R coqprime/src/Coqprime Coqprime -arg -w -arg -all \
  "${sources[@]}" -o Makefile.curves
if ! make -f Makefile.curves -j"$jobs" \
    src/Curves/Montgomery/XZProofs.vo src/Spec/Curve25519.vo > ../fiat-build.log 2>&1; then
  tail -n 60 ../fiat-build.log >&2
  exit 1
fi
