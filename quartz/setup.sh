#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

revision=7db2fa703550655e0c578607da42bc3a63c37307
dependency="$PWD/.deps/quartz"
patch="$PWD/quartz/constant_time_multiplier.patch"
mkdir -p .deps
if [[ ! -d "$dependency" ]]; then
  git clone https://github.com/mit-plv/quartz.git "$dependency"
  git -C "$dependency" checkout --detach "$revision"
fi
if [[ "$(git -C "$dependency" rev-parse HEAD)" != "$revision" ]]; then
  printf 'Quartz must be at %s; existing checkout left unchanged.\n' "$revision" >&2
  exit 1
fi
if git -C "$dependency" diff --quiet HEAD; then
  git -C "$dependency" apply --check "$patch"
  git -C "$dependency" apply "$patch"
elif ! git -C "$dependency" apply --reverse --check "$patch"; then
  printf 'Quartz has incompatible local changes; checkout left unchanged.\n' >&2
  exit 1
fi

cd -- "$dependency"
dune build examples/Processor.vo
