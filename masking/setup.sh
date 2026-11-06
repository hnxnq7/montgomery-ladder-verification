#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
switch="$PWD/.deps/masking-toolchain"

if [[ ! -d "$switch/_opam" ]]; then
  opam switch create "$switch" ocaml-base-compiler.5.3.0 -y
fi
opam repository add rocq-released https://rocq-prover.org/opam/released --switch="$switch" -y
opam update rocq-released --switch="$switch"

# Some macOS toolchains need the SDK's C++ headers for Flocq's build tool.
if [[ "$(uname -s)" == Darwin ]]; then
  sdk="$(xcrun --show-sdk-path)"
  export CXX="${CXX:-clang++} -isystem $sdk/usr/include/c++/v1"
fi

opam install --switch="$switch" -y --jobs=4 \
  rocq-core.9.1.0 rocq-stdlib.9.1.0 rocq-mathcomp-algebra.2.6.0 \
  rocq-mathcomp-analysis.1.19.0 rocq-infotheo.0.9.9
