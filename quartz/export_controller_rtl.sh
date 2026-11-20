#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "$0")/.." && pwd)"
out="$root/.deps/quartz-controller-rtl"
toolchain="$root/.deps/quartz-toolchain/_opam/bin"
emit_only=false
if [[ "$#" != 0 ]]; then
  if [[ "$#" == 1 && "$1" == --emit-only ]]; then emit_only=true
  else printf 'Usage: bash quartz/export_controller_rtl.sh [--emit-only]\n' >&2; exit 2
  fi
fi
export OCAMLPATH="$root/.deps/quartz/_build/install/default/lib${OCAMLPATH:+:$OCAMLPATH}"
for artifact in quartz/controller_protection.vo .deps/quartz-math/curve25519_math.vo \
    .deps/quartz/_build/default/lang/sv.vo; do
  if [[ ! -f "$root/$artifact" ]]; then
    printf 'Missing prerequisite: %s. Build it in the Quartz toolchain first.\n' "$artifact" >&2
    exit 1
  fi
done
mkdir -p "$out"
cd -- "$root/.deps/quartz-math"
paths=(-Q . "" -Q "$root/.deps/quartz/_build/default/lang" quartz.lang
  -Q "$root/.deps/quartz/_build/default/examples" quartz.examples -Q "$root/quartz" LadderQuartz
  -R .deps/fiat-crypto/src Crypto -Q .deps/fiat-crypto/rewriter/src/Rewriter Rewriter
  -R .deps/fiat-crypto/coqprime/src/Coqprime Coqprime)
if ! "$toolchain/rocq" compile "${paths[@]}" "$root/quartz/controller_rtl_export.v" \
    > "$out/proofs.log" 2>&1; then
  printf 'Controller export proof build failed; see %s/proofs.log\n' "$out" >&2
  exit 1
fi
temporary="$(mktemp "$out/emission.XXXXXX")"
trap 'rm -f "$temporary"' EXIT
if ! printf '%s\n' 'Require Import LadderQuartz.controller_rtl_export.' \
  'From quartz.lang Require Import Syntax sv.' \
  'Import Strings.String. Local Open Scope string_scope.' \
  'Compute ControllerRTL.systemverilog (sv.pp (ControllerRTL.native_circuit (var := sv.var) (func := sv.fn))).' |
  python3 -c '
import re
import subprocess
import sys

result = subprocess.run([sys.argv[1], "repl", *sys.argv[3:]], input=sys.stdin.read(),
                        text=True, capture_output=True)
matches = re.findall(r"^\s*=\s*\"((?:[^\"]|\"\")*)\"(?:\s*:\s*string)?",
                     result.stdout, re.MULTILINE)
if result.returncode or "Error:" in result.stderr or not matches:
    sys.stderr.write(result.stderr + result.stdout)
    sys.exit(1)
native = matches[-1].replace("\"\"", "\"") + "\n"
with open(sys.argv[2], "w") as raw:
    raw.write(native)
if "`error" in native:
    sys.exit("Native backend rejected a construct; inspect raw output")

either = re.compile(r"^class Either #\(parameter type A, parameter type B\);\n.*?^endclass\n",
                    re.MULTILINE | re.DOTALL)
candidate, count = either.subn("", native)
removed_either = count == 1 and not re.search(r"\bEither\b", candidate)
rtl = candidate if removed_either else native

# Alias innermost Pair types first, preserving the native type expressions.
# Insert each alias only after its native struct dependencies are declared.
prefix = "quartz_controller_pair_type_"
if prefix in rtl:
    sys.exit("Pair alias prefix collision")
pair = re.compile(r"Pair#\(([^()\n]+), ([^()\n]+)\)::t")
struct = re.compile(r"^typedef struct packed \{.*\} ([A-Za-z_][A-Za-z_0-9]*);$")
struct_names = {m.group(1) for line in rtl.splitlines() if (m := struct.match(line))}
aliases, by_type, emitted, defined_structs, lines = {}, {}, set(), set(), []

def dependencies(value):
    return set(re.findall(r"\b[A-Za-z_][A-Za-z_0-9]*\b", value))

def emit_alias(name):
    if name in emitted:
        return
    for dep in sorted(dependencies(aliases[name])):
        if dep in aliases:
            emit_alias(dep)
        elif dep in struct_names and dep not in defined_structs:
            sys.exit(f"Pair alias requires undeclared native type: {dep}")
    lines.append(f"typedef {aliases[name]} {name};")
    emitted.add(name)

for line in rtl.splitlines():
    original = line
    while True:
        match = pair.search(line)
        if not match:
            break
        value = match.group(0)
        if value not in by_type:
            name = f"{prefix}{len(aliases)}"
            by_type[value] = name
            aliases[name] = value
        line = line[:match.start()] + by_type[value] + line[match.end():]
    for name in sorted(dependencies(line) & aliases.keys()):
        emit_alias(name)
    lines.append(line)
    declaration = struct.match(original)
    if declaration:
        defined_structs.add(declaration.group(1))
rtl = "\n".join(lines) + "\n"

# Verify the emitted declarations and reverse the actual transformation.
alias_decl = re.compile(r"^typedef (Pair#\([^\n]+\)::t) (quartz_controller_pair_type_\d+);\n",
                        re.MULTILINE)
actual = alias_decl.findall(rtl)
if len(actual) != len(aliases) or {name: value for value, name in actual} != aliases:
    sys.exit("Native preservation failed: alias declarations differ")
restored = alias_decl.sub("", rtl)
for name, value in reversed(list(aliases.items())):
    restored = re.sub(rf"\b{name}\b", lambda _: value, restored)
expected = candidate if removed_either else native
if [s for s in restored.splitlines() if s] != [s for s in expected.splitlines() if s]:
    sys.exit("Native preservation failed: circuit text changed")
sys.stderr.write(f"PASS: reverse-alias native preservation ({len(aliases)} aliases; "
                 f"unused Either removed={removed_either}).\n")
sys.stdout.write(rtl)
' "$toolchain/rocq" "$out/protected_ladder_controller.raw.sv" -q -quiet "${paths[@]}" \
    > "$temporary" 2> "$out/emission.log"; then
  printf 'Native export failed; see %s/emission.log. No new RTL installed.\n' "$out" >&2
  exit 1
fi
mv -- "$temporary" "$out/protected_ladder_controller.sv"
printf 'Generated %s/protected_ladder_controller.sv\n' "$out"
if [[ "$emit_only" == true ]]; then
  printf 'Emission only; no elaboration or simulation claim.\n'
  exit 0
fi
verilator="${VERILATOR:-verilator}"
if ! command -v "$verilator" >/dev/null 2>&1; then
  printf 'RTL emitted; Verilator unavailable. No simulation claim.\n' >&2
  exit 1
fi
"$verilator" --version > "$out/simulator-version.log"
compiler_flags=()
if [[ -n "${CXX:-}" ]]; then
  compiler_flags=(-MAKEFLAGS "CXX=$CXX LINK=$CXX")
  "$CXX" --version > "$out/compiler-version.log"
fi
if ! "$verilator" --binary --timing --top-module controller_rtl_smoke --Mdir "$out/obj_dir" \
    "${compiler_flags[@]}" "$out/protected_ladder_controller.sv" "$root/quartz/controller_rtl_smoke.sv" \
    > "$out/elaboration.log" 2>&1; then
  printf 'Controller RTL elaboration failed; see %s/elaboration.log\n' "$out" >&2
  exit 1
fi
"$out/obj_dir/Vcontroller_rtl_smoke" | tee "$out/simulation.log"
