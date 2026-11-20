#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "$0")/.." && pwd)"
base="${QUARTZ_BASE_DIR:-$root/.deps/quartz-masked-arithmetic}"
lock="$base/.masked-build-lock"
if ! mkdir "$lock" 2>/dev/null; then
  printf 'Build/export lock exists or base is missing: %s; refusing export.\n' "$lock" >&2
  exit 1
fi
trap 'rmdir "$lock"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
if [[ -n "${MASKED_BUILD_DIR:-}" ]]; then
  build="$MASKED_BUILD_DIR"
elif [[ -f "$base/latest-checked.txt" ]]; then
  build=$(cat "$base/latest-checked.txt")
else
  printf 'No checked manifest snapshot; run bash quartz/check_masked_arithmetic.sh first.\n' >&2
  exit 1
fi
printer="$base/quartz/_build/default/lang"
if [[ -f "$build/printer/sv.vo" ]]; then printer="$build/printer"; fi
out="$build/rtl"
rocq="$root/.deps/masking-toolchain/_opam/bin/rocq"
export OCAMLPATH="$base/quartz/_build/install/default/lib"
fiat="$base/math/.deps/fiat-crypto"
paths=(-Q "$base/math" "" -R "$fiat/src" Crypto
  -Q "$fiat/rewriter/src/Rewriter" Rewriter -R "$fiat/coqprime/src/Coqprime" Coqprime
  -Q "$base/quartz/_build/default/lang" quartz.lang
  -Q "$base/quartz/_build/default/examples" quartz.examples
  -Q "$build/project" LadderQuartz -Q "$build/masking" Masking)
if [[ "$printer" != "$base/quartz/_build/default/lang" ]]; then paths+=(-Q "$printer" quartz.lang); fi
for artifact in "$build/project/masked_arithmetic_rtl_export.vo" "$printer/sv.vo"; do
  if [[ ! -f "$artifact" ]]; then
    printf 'Missing %s; run bash quartz/check_masked_arithmetic.sh first.\n' "$artifact" >&2
    exit 1
  fi
done
verilator="${VERILATOR:-verilator}"
command -v "$verilator" >/dev/null
mkdir -p "$out"
cd -- "$build"
"$verilator" --version > "$out/simulator-version.log"
for module in masked_arithmetic masked_arithmetic_rtl_export; do
  if ! cmp -s "$root/quartz/$module.v" "$build/project/$module.v"; then
    printf 'Missing or stale compiled source snapshot: %s/project/%s.v\n' "$build" "$module" >&2
    exit 1
  fi
done
cp "$root/quartz/masked_arithmetic_smoke.sv" "$out/masked_arithmetic_smoke.sv"
shasum -a 256 "$build/project/masked_arithmetic.v" "$build/project/masked_arithmetic.vo" \
  "$build/project/masked_arithmetic_rtl_export.v" "$build/project/masked_arithmetic_rtl_export.vo" \
  "$out/masked_arithmetic_smoke.sv" "$root/quartz/export_masked_arithmetic.sh" > "$out/sources.sha256"

for k in 2 4; do
  destination="$out/k$k"
  mkdir -p "$destination"
  python3 - "$rocq" "$destination" "$k" "${paths[@]}" <<'PY'
import hashlib
import json
import pathlib
import re
import resource
import subprocess
import sys
import time

rocq, destination, k = sys.argv[1:4]
out = pathlib.Path(destination)
source = ("From quartz.lang Require Import Syntax sv.\n"
          "From LadderQuartz Require Import masked_arithmetic_rtl_export.\n"
          "From Stdlib Require Import String. Local Open Scope string_scope.\n"
          f"Compute sv.pp (@MaskedArithmeticRTL.native{k} sv.var sv.fn).\n")
started = time.monotonic()
result = subprocess.run([rocq, "repl", "-q", "-quiet", *sys.argv[4:]], input=source,
                        text=True, capture_output=True)
elapsed = time.monotonic() - started
(out / "printer.log").write_text(result.stderr)
matches = re.findall(r'^\s*=\s*"((?:[^"]|"")*)"(?:\s*:\s*string)?', result.stdout, re.MULTILINE)
if result.returncode or "Error:" in result.stderr or not matches:
    (out / "printer-failure.log").write_text(result.stdout + result.stderr)
    raise SystemExit(f"Native printing failed: {out / 'printer-failure.log'}")
raw = matches[-1].replace('""', '"') + "\n"
(out / "primitives.raw.sv").write_text(raw)
if "`error" in raw:
    raise SystemExit("Quartz printer rejected a construct; raw output retained")

# Only remove an unused class and introduce reversible aliases for native Pair types.
either = re.compile(r"^class Either #\(parameter type A, parameter type B\);\n.*?^endclass\n",
                    re.MULTILINE | re.DOTALL)
candidate, count = either.subn("", raw)
removed_either = count == 1 and not re.search(r"\bEither\b", candidate)
native = candidate if removed_either else raw
prefix = "quartz_masked_pair_type_"
if prefix in native:
    raise SystemExit("Pair alias prefix collision")
pattern = re.compile(r"Pair#\(([^()\n]+), ([^()\n]+)\)::t")
aliases, by_type, lines = {}, {}, []
for line in native.splitlines():
    while True:
        match = pattern.search(line)
        if not match:
            break
        value = match.group(0)
        if value not in by_type:
            name = f"{prefix}{len(aliases)}"
            by_type[value] = name
            aliases[name] = value
        line = line[:match.start()] + by_type[value] + line[match.end():]
    lines.append(line)
rtl = "\n".join(lines) + "\n"
first_function = re.search(r"^function automatic ", rtl, re.MULTILINE)
if not first_function:
    raise SystemExit("Native output has no function definitions")
alias_block = "".join(f"typedef {value} {name};\n" for name, value in aliases.items())
rtl = rtl[:first_function.start()] + alias_block + rtl[first_function.start():]
declaration = re.compile(r"^typedef (Pair#\([^\n]+\)::t) (quartz_masked_pair_type_\d+);\n",
                         re.MULTILINE)
actual = declaration.findall(rtl)
if len(actual) != len(aliases) or {name: value for value, name in actual} != aliases:
    raise SystemExit("Alias declaration preservation failed")
restored = declaration.sub("", rtl)
for name, value in reversed(list(aliases.items())):
    restored = re.sub(rf"\b{name}\b", lambda _: value, restored)
if restored.splitlines() != native.splitlines():
    raise SystemExit("Reverse alias check failed: native circuit text changed")
entries = re.findall(r"^function automatic .*? ([A-Za-z_][A-Za-z_0-9]*)\s*\(", rtl, re.MULTILINE)
if len(entries) != len(set(entries)):
    raise SystemExit("Native function name collision")
if not entries or entries[-1] != f"specialized{k}":
    raise SystemExit(f"Unexpected native entry point: {entries[-1:]}")
(out / "primitives.sv").write_text(rtl)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
metrics = {"shares": int(k), "harness": "combined add/sub/multiply/refresh",
           "printer_seconds": elapsed, "printer_child_peak_rss_bytes": rss if sys.platform == "darwin" else rss * 1024,
           "raw_bytes": len(raw.encode()), "functions": len(entries), "pair_aliases": len(aliases),
           "raw_sha256": hashlib.sha256(raw.encode()).hexdigest(), "unused_either_removed": removed_either}
(out / "emission.json").write_text(json.dumps(metrics, indent=2) + "\n")
print(json.dumps(metrics))
PY
  compiler_flags=()
  object_dir="$(mktemp -d "$destination/obj.XXXXXX")"
  printf '%s\n' "$object_dir" > "$destination/build-directory.txt"
  printf 'CXX=%s\nLDFLAGS=%s\n' "${CXX:-verilator default}" "${LDFLAGS:-}" \
    > "$destination/compiler-configuration.log"
  if [[ -n "${CXX:-}" ]]; then
    compiler_flags=(-MAKEFLAGS "CXX=$CXX LINK=$CXX")
    "$CXX" --version > "$destination/compiler-version.log"
  fi
  python3 - "$destination" "$verilator" --binary --top-module masked_arithmetic_smoke \
    --Mdir "$object_dir" -j "${JOBS:-2}" \
    "-DQUARTZ_SHARES=$k" "-DQUARTZ_ENTRY=specialized$k" "${compiler_flags[@]}" \
    "$destination/primitives.sv" "$out/masked_arithmetic_smoke.sv" <<'PY'
import json
import pathlib
import resource
import subprocess
import sys
import time

out = pathlib.Path(sys.argv[1])
started = time.monotonic()
with (out / "elaboration.log").open("w") as log:
    result = subprocess.run(sys.argv[2:], stdout=log, stderr=subprocess.STDOUT)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
(out / "elaboration.json").write_text(json.dumps({"seconds": time.monotonic() - started,
    "child_peak_rss_bytes": rss if sys.platform == "darwin" else rss * 1024,
    "exit_code": result.returncode}, indent=2) + "\n")
if result.returncode:
    raise SystemExit(f"Elaboration failed: {out / 'elaboration.log'}")
PY
  "$object_dir/Vmasked_arithmetic_smoke" | tee "$destination/simulation.log"
done
printf 'Two/four-share combinational exports tested; no secure-controller or physical timing claim.\n'
