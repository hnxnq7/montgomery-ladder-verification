#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
switch="$root/.deps/masking-toolchain"
if [[ "${OPAM_SWITCH_PREFIX:-}" != "$switch/_opam" ]]; then
  exec opam exec --switch="$switch" -- bash "$root/quartz/check_masked_arithmetic.sh" "$@"
fi
with_controller=false
with_security=false
with_execution=false
with_ladder=false
with_native=false
for option in "$@"; do
  case "$option" in
    --with-controller) with_controller=true ;;
    --with-bank-security) with_controller=true; with_security=true ;;
    --with-execution-security) with_controller=true; with_security=true; with_execution=true ;;
    --with-ladder-security)
      with_controller=true; with_security=true; with_execution=true; with_ladder=true ;;
    --with-native-export) with_controller=true; with_native=true ;;
    *) printf 'Usage: bash quartz/check_masked_arithmetic.sh [OPTION]\n' >&2
       printf 'Options: --with-controller, --with-bank-security, --with-execution-security, --with-ladder-security, --with-native-export\n' >&2
       exit 2 ;;
  esac
done

build="$root/.deps/quartz-masked-arithmetic"
mkdir -p "$build/math" "$build/project" "$build/masking" "$build/logs"
lock="$build/.masked-build-lock"
if ! mkdir "$lock" 2>/dev/null; then
  printf 'Build/export lock exists: %s; refusing concurrent dependency writes.\n' "$lock" >&2
  exit 1
fi
trap 'rmdir "$lock"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
bootstrap=$(mktemp -d "$build/bootstrap.XXXXXX")
rocq --version > "$bootstrap/rocq-version.txt"
opam list --switch="$switch" --installed --columns=name,version --color=never \
  > "$bootstrap/opam-packages.txt"
fingerprint=$(shasum -a 256 "$switch/_opam/lib/coq/theories/Init/Prelude.vo" "$switch/_opam/bin/ocamlopt")
if [[ -f "$build/toolchain.txt" && "$(cat "$build/toolchain.txt")" != "$fingerprint" ]]; then
  printf 'Compiler foundations changed; use a fresh .deps/quartz-masked-arithmetic directory.\n' >&2
  exit 1
fi
printf '%s\n' "$fingerprint" > "$build/toolchain.txt"

checkout() {
  local destination="$1" url="$2" revision="$3" cache="$4"
  if [[ ! -d "$destination/.git" && ! -f "$destination/.git" ]]; then
    if [[ -d "$cache" ]]; then git clone --no-hardlinks "$cache" "$destination"
    else git clone "$url" "$destination"
    fi
    git -C "$destination" checkout --detach "$revision"
  fi
  if [[ "$(git -C "$destination" rev-parse HEAD)" != "$revision" ]]; then
    printf 'Unexpected dependency revision: %s\n' "$destination" >&2
    exit 1
  fi
}

check_untracked() {
  local destination="$1" file
  while IFS= read -r -d '' file; do
    case "$file" in
      Makefile.curves|Makefile.curves.conf)
        [[ "$destination" == "$build/math/.deps/fiat-crypto" ]] && continue ;;
    esac
    printf 'Unexpected dependency file: %s/%s\n' "$destination" "$file" >&2
    exit 1
  done < <(git -C "$destination" ls-files --others --exclude-standard -z)
}

checkout "$build/quartz" https://github.com/mit-plv/quartz.git \
  7db2fa703550655e0c578607da42bc3a63c37307 "$root/.deps/quartz-noise/quartz"
patch="$root/quartz/constant_time_multiplier.patch"
if git -C "$build/quartz" diff --quiet HEAD; then
  git -C "$build/quartz" apply --check "$patch"
  git -C "$build/quartz" apply "$patch"
fi
index_dir=$(mktemp -d "$build/patch-index.XXXXXX")
GIT_INDEX_FILE="$index_dir/index" git -C "$build/quartz" read-tree HEAD
GIT_INDEX_FILE="$index_dir/index" git -C "$build/quartz" apply --cached "$patch"
expected_tree=$(GIT_INDEX_FILE="$index_dir/index" git -C "$build/quartz" write-tree)
if ! git -C "$build/quartz" diff --quiet "$expected_tree" --; then
  printf 'Unexpected Quartz modifications in isolated build.\n' >&2
  exit 1
fi
check_untracked "$build/quartz"
printf '%s\n' "$expected_tree" > "$bootstrap/quartz-patched-tree.txt"
shasum -a 256 "$patch" "$root/setup_fiat_crypto.sh" "${BASH_SOURCE[0]}" > "$bootstrap/tools.sha256"
(cd "$build/quartz" && dune build examples/Processor.vo lang/transform.vo lang/sv.vo) \
  > "$bootstrap/quartz.log" 2>&1
export OCAMLPATH="$build/quartz/_build/install/default/lib"

fiat="$build/math/.deps/fiat-crypto"
cache="$root/.deps/quartz-noise/math/.deps/fiat-crypto"
mkdir -p "$build/math/.deps"
checkout "$fiat" https://github.com/mit-plv/fiat-crypto.git \
  9d0682462646bf645cba7409fa45794dee0418aa "$cache"
for sub in coqprime rewriter; do
  revision=$(git -C "$fiat" rev-parse "HEAD:$sub")
  url=$(git -C "$fiat" config -f .gitmodules --get "submodule.$sub.url")
  checkout "$fiat/$sub" "$url" "$revision" "$cache/$sub"
  git -C "$fiat/$sub" diff --quiet HEAD
  check_untracked "$fiat/$sub"
done
git -C "$fiat" diff --quiet HEAD
check_untracked "$fiat"
cp "$root/setup_fiat_crypto.sh" "$root/ladder_math.v" "$root/curve25519_math.v" "$build/math/"
bash "$build/math/setup_fiat_crypto.sh" > "$bootstrap/fiat.log" 2>&1

# Each invocation preserves its own sources and excludes stale project artifacts.
snapshot=$(mktemp -d "$build/snapshot.XXXXXX")
mkdir -p "$snapshot/project" "$snapshot/masking" "$snapshot/logs"
printf '%s\n' "$bootstrap" > "$snapshot/logs/bootstrap.txt"
printf 'controller=%s\nbank_security=%s\nexecution_security=%s\nladder_security=%s\nnative_export=%s\n' \
  "$with_controller" "$with_security" "$with_execution" "$with_ladder" "$with_native" \
  > "$snapshot/logs/configuration.txt"
quartz_modules=(accelerator accelerator_correctness hamming_weight packed_storage
  masked_arithmetic masked_arithmetic_rtl_export masked_bank masked_ladder)
masking_modules=(finite_masking shared_ladder trace_masking noisy_leakage noisy_bit_example
  xor_shares noisy_shares noisy_channel_bridge noisy_trace noisy_history_budget history_semantics
  arithmetic_shares arithmetic_privacy arithmetic_refresh noisy_common_mass arithmetic_channel
  arithmetic_bank_refresh fiat_field cube_encoding quartz_hw_encoding quartz_masked_hw
  arithmetic_control arithmetic_ladder)
libraries=(LadderQuartz.masked_arithmetic LadderQuartz.masked_arithmetic_rtl_export
  LadderQuartz.masked_bank LadderQuartz.masked_ladder Masking.quartz_masked_hw)
if [[ "$with_controller" == true ]]; then
  quartz_modules+=(masked_controller masked_controller_storage masked_controller_schedule
    masked_controller_program masked_controller_rtl_export masked_controller_functional masked_controller_tick_program
    masked_controller_layout_tests)
  libraries+=(LadderQuartz.masked_controller LadderQuartz.masked_controller_storage
    LadderQuartz.masked_controller_schedule LadderQuartz.masked_controller_program
    LadderQuartz.masked_controller_rtl_export LadderQuartz.masked_controller_functional
    LadderQuartz.masked_controller_tick_program LadderQuartz.masked_controller_layout_tests)
fi
if [[ "$with_security" == true ]]; then
  masking_modules+=(arithmetic_product_bound arithmetic_aggregate arithmetic_spectral cyclic_characters
    field_characters field_coefficient field_aggregate_spectral field_refresh field_mul_gadget
    field_history cube_spectral cube_roots cube_bound cube_field_bound cube_strong_bound
    curve_coefficient curve_snapshot curve25519_snapshot curve_bank_bound quartz_masked_bank_security)
  libraries+=(Masking.quartz_masked_bank_security)
fi
if [[ "$with_execution" == true ]]; then
  masking_modules+=(curve_snapshot_budget curve_trace_budget curve_bank_history
    quartz_masked_execution quartz_masked_budget)
  libraries+=(Masking.curve_snapshot_budget Masking.curve_trace_budget Masking.curve_bank_history
    Masking.quartz_masked_execution Masking.quartz_masked_budget)
fi
if [[ "$with_ladder" == true ]]; then
  quartz_modules+=(masked_controller_loop masked_controller_curve
    accelerator_ladder_bridge ladder_controller controller_protection)
  masking_modules+=(ladder_distribution shared_power shared_loop ladder_trace ladder_bridge
    masked_curve25519 quartz_masked_ladder_security quartz_noise_bridge quartz_comparison)
  libraries+=(LadderQuartz.masked_controller_loop LadderQuartz.masked_controller_curve
    Masking.ladder_bridge Masking.masked_curve25519 Masking.quartz_masked_ladder_security
    Masking.quartz_noise_bridge Masking.quartz_comparison)
fi
if [[ "$with_native" == true ]]; then
  quartz_modules+=(masked_arithmetic_native masked_controller_native masked_controller_native_export sv_printer)
  libraries+=(LadderQuartz.masked_arithmetic_native LadderQuartz.masked_controller_native
    LadderQuartz.masked_controller_native_export LadderQuartz.sv_printer)
fi
sources=()
for module in "${quartz_modules[@]}"; do
  cp "$root/quartz/$module.v" "$snapshot/project/"
  sources+=("$snapshot/project/$module.v")
done
for module in "${masking_modules[@]}"; do
  cp "$root/masking/$module.v" "$snapshot/masking/"
  sources+=("$snapshot/masking/$module.v")
done
paths=(-Q "$build/math" "" -R "$fiat/src" Crypto
  -Q "$fiat/rewriter/src/Rewriter" Rewriter -R "$fiat/coqprime/src/Coqprime" Coqprime
  -Q "$build/quartz/_build/default/lang" quartz.lang
  -Q "$build/quartz/_build/default/examples" quartz.examples
  -Q "$snapshot/project" LadderQuartz -Q "$snapshot/masking" Masking)
cd -- "$snapshot"
printf '%s\n' "${paths[@]}" > "$snapshot/logs/loadpaths.txt"
git -C "$build/quartz" rev-parse HEAD > "$snapshot/logs/quartz-revision.txt"
git -C "$fiat" rev-parse HEAD > "$snapshot/logs/fiat-revision.txt"
printf '%s\n' "${sources[@]}" > "$snapshot/logs/source-manifest.txt"
shasum -a 256 "${sources[@]}" "$build/math/ladder_math.v" "$build/math/curve25519_math.v" \
  > "$snapshot/logs/sources.sha256"
rocq compile "${paths[@]}" "$build/math/ladder_math.v" > "$snapshot/logs/ladder-math.log" 2>&1
rocq compile "${paths[@]}" "$build/math/curve25519_math.v" > "$snapshot/logs/curve-math.log" 2>&1
coq_makefile "${paths[@]}" "${sources[@]}" -o Makefile.masked \
  > "$snapshot/logs/dependencies.log" 2>&1

targets=()
for library in "${libraries[@]}"; do
  case "$library" in
    LadderQuartz.*) targets+=("$snapshot/project/${library#LadderQuartz.}.vo") ;;
    Masking.*) targets+=("$snapshot/masking/${library#Masking.}.vo") ;;
  esac
done
printf '%s\n' "${libraries[@]}" > "$snapshot/logs/checked-targets.txt"
printf 'Checking isolated snapshot: %s\n' "$snapshot"
if ! make -f Makefile.masked -j "${JOBS:-2}" "${targets[@]}" > "$snapshot/logs/project.log" 2>&1; then
  tail -n 60 "$snapshot/logs/project.log" >&2
  exit 1
fi
rocqchk -silent "${paths[@]}" "${libraries[@]}" > "$snapshot/logs/kernel.log" 2>&1
printf '%s\n' "$snapshot" > "$build/latest-checked.$$.txt"
mv "$build/latest-checked.$$.txt" "$build/latest-checked.txt"
printf 'Source-only isolated build and full recursive kernel check passed: %s\n' "$snapshot"
printf 'Checked targets are listed in %s/logs/checked-targets.txt.\n' "$snapshot"
