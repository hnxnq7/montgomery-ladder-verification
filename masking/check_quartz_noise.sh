#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
root="$PWD"
switch="$root/.deps/masking-toolchain"
if [[ "${OPAM_SWITCH_PREFIX:-}" != "$switch/_opam" ]]; then
  exec opam exec --switch="$switch" -- bash "$root/masking/check_quartz_noise.sh" "$@"
fi

build="$root/.deps/quartz-noise"
mkdir -p "$build/math" "$build/project" "$build/masking"
# Never reuse artifacts after changing the compiler or its foundational libraries.
fingerprint=$(shasum -a 256 "$switch/_opam/lib/coq/theories/Init/Prelude.vo" \
  "$switch/_opam/bin/ocamlopt")
if [[ -f "$build/toolchain.txt" && "$(cat "$build/toolchain.txt")" != "$fingerprint" ]]; then
  printf 'Toolchain changed; use a fresh .deps/quartz-noise build directory.\n' >&2
  exit 1
fi
printf '%s\n' "$fingerprint" > "$build/toolchain.txt"

checkout() {
  local destination="$1" url="$2" revision="$3" cache="$4"
  if [[ ! -d "$destination/.git" && ! -f "$destination/.git" ]]; then
    if [[ -d "$cache" ]]; then
      git clone --no-hardlinks "$cache" "$destination"
    else
      git clone "$url" "$destination"
    fi
    git -C "$destination" checkout --detach "$revision"
  fi
  if [[ "$(git -C "$destination" rev-parse HEAD)" != "$revision" ]]; then
    printf 'Unexpected dependency revision: %s\n' "$destination" >&2
    exit 1
  fi
}

checkout "$build/quartz" https://github.com/mit-plv/quartz.git \
  7db2fa703550655e0c578607da42bc3a63c37307 "$root/.deps/quartz"
patch="$root/quartz/constant_time_multiplier.patch"
if git -C "$build/quartz" diff --quiet HEAD; then
  git -C "$build/quartz" apply --check "$patch"
  git -C "$build/quartz" apply "$patch"
elif ! git -C "$build/quartz" apply --reverse --check "$patch"; then
  printf 'Unexpected Quartz source modifications in isolated build.\n' >&2
  exit 1
fi
(cd "$build/quartz"; dune build examples/Processor.vo lang/transform.vo)
export OCAMLPATH="$build/quartz/_build/install/default/lib"

fiat="$build/math/.deps/fiat-crypto"
cache="$root/.deps/quartz-math/.deps/fiat-crypto"
mkdir -p "$build/math/.deps"
checkout "$fiat" https://github.com/mit-plv/fiat-crypto.git \
  9d0682462646bf645cba7409fa45794dee0418aa "$cache"
for sub in coqprime rewriter; do
  revision=$(git -C "$fiat" rev-parse "HEAD:$sub")
  url=$(git -C "$fiat" config -f .gitmodules --get "submodule.$sub.url")
  checkout "$fiat/$sub" "$url" "$revision" "$cache/$sub"
done
cp "$root/setup_fiat_crypto.sh" "$root/ladder_math.v" "$root/curve25519_math.v" "$build/math/"
bash "$build/math/setup_fiat_crypto.sh"
paths=(-Q "$build/math" "" -R "$fiat/src" Crypto -Q "$fiat/rewriter/src/Rewriter" Rewriter
  -R "$fiat/coqprime/src/Coqprime" Coqprime
  -Q "$build/quartz/_build/default/lang" quartz.lang
  -Q "$build/quartz/_build/default/examples" quartz.examples
  -Q "$build/project" LadderQuartz -Q "$build/masking" Masking)
# The repository root contains incompatible unqualified ladder_math artifacts.
cd "$build"
rocq compile "${paths[@]}" "$build/math/ladder_math.v"
rocq compile "${paths[@]}" "$build/math/curve25519_math.v"
for module in accelerator accelerator_correctness accelerator_ladder_bridge hamming_weight \
    packed_storage ladder_controller controller_protection; do
  cp "$root/quartz/$module.v" "$build/project/"
  rocq compile "${paths[@]}" "$build/project/$module.v"
done
for module in finite_masking noisy_leakage noisy_bit_example xor_shares noisy_shares \
    noisy_channel_bridge cube_encoding quartz_hw_encoding quartz_noise_bridge; do
  cp "$root/masking/$module.v" "$build/masking/"
  rocq compile -q -w -notation-overridden,-ambiguous-paths "${paths[@]}" "$build/masking/$module.v"
done
rocqchk -silent "${paths[@]}" Masking.quartz_hw_encoding Masking.quartz_noise_bridge
printf 'Quartz/Infotheo bridge build and kernel check passed.\n'
