#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "$0")/.." && pwd)"
cd -- "$root"
check=true
if [[ "$#" != 0 ]]; then
  if [[ "$#" == 1 && "$1" == --emit-only ]]; then
    check=false
  else
    printf 'Usage: bash quartz/export_rtl.sh [--emit-only]\n' >&2
    exit 2
  fi
fi
toolchain="$root/.deps/quartz-toolchain"
out="$root/.deps/quartz-rtl"
run() { opam exec --switch="$toolchain" -- "$@"; }
export OCAMLPATH="$root/.deps/quartz/_build/install/default/lib"
if [[ ! -f quartz/protected_accelerator.vo ]]; then
  printf 'Build quartz/protected_accelerator.v in the Quartz toolchain first.\n' >&2
  exit 1
fi
mkdir -p "$out"
run dune build --root "$root/.deps/quartz" lang/sv.vo
run rocq compile -Q .deps/quartz/_build/default/lang quartz.lang \
  -Q .deps/quartz/_build/default/examples quartz.examples \
  -Q quartz LadderQuartz quartz/rtl_export.v
temporary="$(mktemp "$out/emission.XXXXXX")"
trap 'rm -f "$temporary"' EXIT
if ! printf '%s\n' 'Require Import LadderQuartz.rtl_export.' \
  'From quartz.lang Require Import Syntax sv.' \
  'Import Strings.String. Local Open Scope string_scope.' \
  'Compute AcceleratorRTL.systemverilog (sv.pp (AcceleratorRTL.native_circuit (var := sv.var) (func := sv.fn))).' |
  run python3 -c '
import re
import subprocess
import sys

result = subprocess.run(
    ["rocq", "repl", *sys.argv[2:]], input=sys.stdin.read(),
    text=True, capture_output=True,
)
matches = re.findall(r"^\s*=\s*\"((?:[^\"]|\"\")*)\"(?:\s*:\s*string)?",
                     result.stdout, re.MULTILINE)
if result.returncode or "Error:" in result.stderr or not matches:
    sys.stderr.write(result.stderr)
    sys.stderr.write(result.stdout)
    sys.exit(1)
rtl = matches[-1].replace("\"\"", "\"") + "\n"
native_rtl = rtl
with open(sys.argv[1], "w") as raw:
    raw.write(rtl)
# Quartz emits this helper even for circuits with no Either types. Verilator
# rejects tagged unions; remove only an unreferenced helper, never circuit code.
either = re.compile(r"^class Either #\(parameter type A, parameter type B\);\n.*?^endclass\n", re.MULTILINE | re.DOTALL)
without_either, count = either.subn("", rtl)
removed_either = count == 1 and not re.search(r"\bEither\b", without_either)
if removed_either:
    rtl = without_either
    sys.stderr.write("Removed unused Either prelude; raw native output retained.\n")
# Give primitive Pair types aliases before they parameterize another Pair.
# This avoids Verilators circular-type diagnostic without changing layouts.
pair_types = sorted(set(re.findall(r"Pair#\(bit\[\d+:0\], bit\[\d+:0\]\)::t", rtl)))
aliases = []
for i, pair_type in enumerate(pair_types):
    alias = f"quartz_pair_type_{i}"
    if re.search(rf"\b{alias}\b", rtl):
        sys.exit("Generated Pair alias name collision")
    rtl = rtl.replace(pair_type, alias)
    aliases.append(f"typedef {pair_type} {alias};")
if aliases:
    pair_end = rtl.find("endclass\n")
    if pair_end < 0 or not rtl.startswith("class Pair #", rtl.find("class ")):
        sys.exit("Native Pair prelude not found")
    pair_end += len("endclass\n")
    rtl = rtl[:pair_end] + "\n" + "\n".join(aliases) + "\n" + rtl[pair_end:]
    sys.stderr.write(f"Named {len(aliases)} primitive Pair types; layouts unchanged.\n")
# Reverse the actual emitted aliases, not the transformation bookkeeping.
alias_decl = re.compile(r"^typedef (Pair#\(bit\[\d+:0\], bit\[\d+:0\]\)::t) (quartz_pair_type_\d+);\n", re.MULTILINE)
emitted_aliases = alias_decl.findall(rtl)
if len(emitted_aliases) != len(pair_types):
    sys.exit("Native preservation failed: unexpected alias declarations")
restored = alias_decl.sub("", rtl)
for pair_type, alias in emitted_aliases:
    restored = re.sub(rf"\b{alias}\b", lambda _: pair_type, restored)
expected = either.sub("", native_rtl) if removed_either else native_rtl
if [line for line in restored.splitlines() if line] != [line for line in expected.splitlines() if line]:
    sys.exit("Native preservation failed: circuit text changed")
sys.stderr.write("PASS: reverse-alias native preservation (only unused helper and blank lines removed).\n")
sys.stdout.write(rtl)
' "$out/protected_ladder_accelerator.raw.sv" -q -quiet \
    -Q .deps/quartz/_build/default/lang quartz.lang \
    -Q .deps/quartz/_build/default/examples quartz.examples -Q quartz LadderQuartz \
    > "$temporary" 2> "$out/emission.log"; then
  printf 'Native Quartz export failed; see %s/emission.log. No RTL emitted.\n' "$out" >&2
  exit 1
fi
if grep -q "$(printf '\140')error" "$temporary"; then
  printf 'Native backend reported an unsupported construct; inspect the generated file.\n' >&2
  exit 1
fi
mv -- "$temporary" "$out/protected_ladder_accelerator.sv"
printf 'Generated %s\n' "$out/protected_ladder_accelerator.sv"
if [[ "$check" == false ]]; then
  printf 'Emission only; no RTL elaboration or simulation was checked.\n'
  exit 0
fi
verilator="${VERILATOR:-verilator}"
if command -v "$verilator" >/dev/null 2>&1; then
  "$verilator" --version | tee "$out/simulator-version.log"
  compiler_flags=()
  if [[ -n "${CXX:-}" ]]; then
    compiler_flags=(-MAKEFLAGS "CXX=$CXX LINK=$CXX")
    "$CXX" --version > "$out/compiler-version.log"
  fi
  if ! "$verilator" --binary --timing --top-module rtl_smoke --Mdir "$out/obj_dir" \
      "${compiler_flags[@]}" \
      "$out/protected_ladder_accelerator.sv" quartz/rtl_smoke.sv > "$out/elaboration.log" 2>&1; then
    printf 'RTL emitted, but Verilator elaboration failed; see %s/elaboration.log\n' "$out" >&2
    exit 1
  fi
  "$out/obj_dir/Vrtl_smoke" | tee "$out/simulation.log"
elif command -v iverilog >/dev/null 2>&1; then
  if ! iverilog -g2012 -s rtl_smoke -o "$out/rtl_smoke.vvp" \
      "$out/protected_ladder_accelerator.sv" quartz/rtl_smoke.sv > "$out/elaboration.log" 2>&1; then
    printf 'RTL emitted, but Icarus elaboration failed; see %s/elaboration.log\n' "$out" >&2
    exit 1
  fi
  vvp "$out/rtl_smoke.vvp" | tee "$out/simulation.log"
else
  printf 'RTL emitted; no supported simulator found. No simulation claim.\n' >&2
  exit 1
fi
