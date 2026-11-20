import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

parser = argparse.ArgumentParser()
parser.add_argument('log', type=Path)
parser.add_argument('output', type=Path)
parser.add_argument('--shares', type=int, choices=(2, 4, 256), required=True)
args = parser.parse_args()
log, output = args.log, args.output
text = log.read_text()
matches = re.findall(r'^\s*=\s*"((?:[^"]|"")*)"(?:\s*:\s*string)?', text, re.MULTILINE)
if 'Error:' in text or not matches:
    raise SystemExit('Native printer failed; retain the stage log')
raw = matches[-1].replace('""', '"') + '\n'
output.mkdir(parents=True, exist_ok=True)
(output / 'controller.raw.sv').write_text(raw)
if '`error' in raw:
    raise SystemExit('Native printer rejected a construct')

# Verilator compatibility only; reversing aliases must recover every native circuit line.
either = re.compile(r'^class Either #\(parameter type A, parameter type B\);\n.*?^endclass\n',
                    re.MULTILINE | re.DOTALL)
candidate, count = either.subn('', raw)
removed_either = count == 1 and not re.search(r'\bEither\b', candidate)
native = candidate if removed_either else raw
prefix = 'quartz_controller_pair_type_'
if prefix in native:
    raise SystemExit('Alias prefix collision')
pattern = re.compile(r'Pair#\(([^()\n]+), ([^()\n]+)\)::t')
aliases, by_type, lines = {}, {}, []
for line in native.splitlines():
    while match := pattern.search(line):
        value = match.group(0)
        if value not in by_type:
            name = f'{prefix}{len(aliases)}'
            by_type[value] = name
            aliases[name] = value
        line = line[:match.start()] + by_type[value] + line[match.end():]
    lines.append(line)
rtl = '\n'.join(lines) + '\n'
first_function = re.search(r'^function automatic ', rtl, re.MULTILINE)
if not first_function:
    raise SystemExit('No native functions')
alias_block = ''.join(f'typedef {value} {name};\n' for name, value in aliases.items())
rtl = rtl[:first_function.start()] + alias_block + rtl[first_function.start():]
declaration = re.compile(
    r'^typedef (Pair#\([^\n]+\)::t) (quartz_controller_pair_type_\d+);\n', re.MULTILINE)
actual = declaration.findall(rtl)
if len(actual) != len(aliases) or {name: value for value, name in actual} != aliases:
    raise SystemExit('Alias declaration preservation failed')
restored = declaration.sub('', rtl)
for name, value in reversed(list(aliases.items())):
    restored = re.sub(rf'\b{name}\b', lambda _: value, restored)
if restored.splitlines() != native.splitlines():
    raise SystemExit('Native circuit text changed')
entries = re.findall(r'^function automatic .*? ([A-Za-z_][A-Za-z_0-9]*)\s*\(', rtl, re.MULTILINE)
if len(entries) != len(set(entries)):
    raise SystemExit('Native function name collision')
if not entries or entries[-1] != f'cycle{args.shares}':
    raise SystemExit(f'Unexpected native entry point: {entries[-1:]}')
(output / 'controller.sv').write_text(rtl)
metrics = dict(shares=args.shares, raw_bytes=len(raw.encode()), functions=len(entries),
               pair_aliases=len(aliases), unused_either_removed=removed_either,
               raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),
               adapted_sha256=hashlib.sha256(rtl.encode()).hexdigest(),
               reverse_alias_audit=True)
(output / 'emission.json').write_text(json.dumps(metrics, indent=2) + '\n')
print(json.dumps(metrics))
