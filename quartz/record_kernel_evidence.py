"""Record trusted build-script kernel runs; this helper never runs or authenticates Rocq.

begin SPEC RUN prints a receipt hash. finish RUN --begin-sha256 HASH --exit-code N
--log LOG records the build script's actual wait status. That status and the
inventory's completeness are trusted caller assertions, not proof certificates.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import uuid

from controller_native_validate import digest

SCHEMA = 'quartz-kernel-evidence-v1'


def write_new(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def absolute(path):
    value = Path(path)
    if not value.is_absolute():
        raise ValueError(f'Expected absolute path: {path}')
    return value.resolve()


def validate_loadpaths(args):
    if not isinstance(args, list) or len(args) % 3:
        raise ValueError('Expected ordered -Q/-R directory namespace triples')
    for i in range(0, len(args), 3):
        if args[i] not in ('-Q', '-R') or not isinstance(args[i + 2], str):
            raise ValueError('Unsupported load-path schema')
        absolute(args[i + 1])
    return args


def resolve_module(args, name):
    for i in reversed(range(0, len(args), 3)):
        namespace = args[i + 2]
        if namespace and not name.startswith(namespace + '.'):
            continue
        relative = name[len(namespace) + 1:] if namespace else name
        parts = relative.split('.')
        if not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', part) for part in parts):
            raise ValueError(f'Unsupported module name: {name}')
        candidate = Path(args[i + 1]).joinpath(*parts).with_suffix('.vo')
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError(f'No compiled module on supplied paths: {name}')


def inventory(paths):
    return {str(path): digest(path) if path.is_file() else None for path in sorted(set(paths))}


def inventory_hash(values):
    checksum = hashlib.sha256()
    for part in json.JSONEncoder(sort_keys=True, separators=(',', ':')).iterencode(values):
        checksum.update(part.encode())
    return checksum.hexdigest()


def begin(spec_path, run):
    spec_path = spec_path.resolve(strict=True)
    spec = json.loads(spec_path.read_text())
    if spec.get('schema') != SCHEMA:
        raise ValueError('Unknown evidence specification schema')
    paths = validate_loadpaths(spec['loadpaths'])
    targets = spec['targets']
    if not targets or len(targets) != len(set(targets)) or set(targets) != set(spec['artifacts']):
        raise ValueError('Targets must match the explicit artifact map exactly')
    tools = spec['tools']
    absolute(tools['compiler'])
    absolute(tools['checker'])
    if spec['command'] != [tools['checker'], '-o', '-m', *paths, *targets]:
        raise ValueError('Command does not match full recursive targets and ordered load paths')
    environment = spec['environment']
    if not isinstance(environment.get('OCAMLPATH'), str) or not all(
            isinstance(k, str) and isinstance(v, str) for k, v in environment.items()):
        raise ValueError('Record explicit tool environment including OCAMLPATH')
    files = {absolute(p) for p in spec['inventory']}
    files.update(absolute(p) for p in tools.values())
    files.add(spec_path)
    files.add(Path(__file__).resolve())
    for target, pair in spec['artifacts'].items():
        artifact, source = absolute(pair['artifact']), absolute(pair['source'])
        if resolve_module(paths, target) != artifact or source != artifact.with_suffix('.v'):
            raise ValueError(f'Target/source/artifact resolution mismatch: {target}')
        files.update((artifact, source))
    hashes = inventory(files)
    if not hashes or any(value is None for value in hashes.values()):
        raise ValueError('Inventory contains missing files')
    # Bind every visible compiled module so a later overlay cannot hide a changed dependency.
    modules = {}
    for i in range(0, len(paths), 3):
        directory, namespace = Path(paths[i + 1]), paths[i + 2]
        for artifact in directory.rglob('*.vo'):
            parts = artifact.relative_to(directory).with_suffix('').parts
            if all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', part) for part in parts):
                name = '.'.join(([namespace] if namespace else []) + list(parts))
                resolved = resolve_module(paths, name)
                if str(resolved) not in hashes:
                    raise ValueError(f'Visible module absent from inventory: {resolved}')
                modules[name] = str(resolved)
    run.mkdir()
    record = dict(schema=SCHEMA, run_id=str(uuid.uuid4()), started_utc=datetime.now(timezone.utc).isoformat(),
                  spec=spec, spec_path=str(spec_path), inventory_before=hashes,
                  inventory_before_sha256=inventory_hash(hashes), modules=modules,
                  trust='Caller supplies complete inventory, exact executed command and actual wait status')
    write_new(run / 'begin.json', record)
    return digest(run / 'begin.json')


def finish(run, receipt, exit_code, log):
    if (run / 'result.json').exists():
        raise ValueError('Result already exists; evidence cannot be overwritten')
    start = json.loads((run / 'begin.json').read_text())
    if start.get('schema') != SCHEMA or digest(run / 'begin.json') != receipt:
        raise ValueError('Begin record schema/hash mismatch')
    with log.open('rb') as source, (run / 'kernel.log').open('xb') as destination:
        shutil.copyfileobj(source, destination, 1024 * 1024)
    after = inventory(Path(p) for p in start['inventory_before'])
    changed = [p for p, value in start['inventory_before'].items() if after[p] != value]
    result = dict(schema=SCHEMA, run_id=start['run_id'], begin_sha256=receipt,
                  finished_utc=datetime.now(timezone.utc).isoformat(), exit_code=exit_code,
                  inputs_unchanged=not changed, changed_inputs=changed, inventory_after=after,
                  inventory_after_sha256=inventory_hash(after),
                  kernel_log_sha256=digest(run / 'kernel.log'),
                  status='recorded_success' if exit_code == 0 and not changed else 'recorded_failure')
    write_new(run / 'result.json', result)
    return result


def load_evidence(run):
    start = json.loads((run / 'begin.json').read_text())
    result = json.loads((run / 'result.json').read_text())
    if start.get('schema') != SCHEMA or result.get('schema') != SCHEMA:
        raise ValueError('Unknown evidence record schema')
    if result['run_id'] != start['run_id'] or result['begin_sha256'] != digest(run / 'begin.json'):
        raise ValueError('Mismatched begin/result records')
    if result['exit_code'] != 0 or not result['inputs_unchanged'] or result['status'] != 'recorded_success':
        raise ValueError('Kernel check not successful with unchanged inputs')
    if result['inventory_after'] != start['inventory_before']:
        raise ValueError('Mismatched before/after inventories')
    if (inventory_hash(start['inventory_before']) != start['inventory_before_sha256'] or
            inventory_hash(result['inventory_after']) != result['inventory_after_sha256']):
        raise ValueError('Inventory hash mismatch')
    if digest(run / 'kernel.log') != result['kernel_log_sha256']:
        raise ValueError('Changed kernel log')
    if inventory(Path(p) for p in start['inventory_before']) != start['inventory_before']:
        raise ValueError('Checked input changed')
    spec = start['spec']
    if json.loads(Path(start['spec_path']).read_text()) != spec:
        raise ValueError('Changed recorded command/specification')
    validate_loadpaths(spec['loadpaths'])
    if (set(spec['targets']) != set(spec['artifacts']) or spec['command'] !=
            [spec['tools']['checker'], '-o', '-m', *spec['loadpaths'], *spec['targets']]):
        raise ValueError('Mismatched recursive command/targets')
    for target, pair in spec['artifacts'].items():
        artifact, source = absolute(pair['artifact']), absolute(pair['source'])
        if (resolve_module(spec['loadpaths'], target) != artifact or
                source != artifact.with_suffix('.v') or
                any(str(p) not in start['inventory_before'] for p in (artifact, source))):
            raise ValueError('Missing or mismatched target artifact inventory binding')
    if any(path not in start['inventory_before'] for path in start['modules'].values()):
        raise ValueError('Module missing from recorded inventory')
    return start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    first = commands.add_parser('begin')
    first.add_argument('spec', type=Path)
    first.add_argument('run', type=Path)
    last = commands.add_parser('finish')
    last.add_argument('run', type=Path)
    last.add_argument('--begin-sha256', required=True)
    last.add_argument('--exit-code', type=int, required=True)
    last.add_argument('--log', type=Path, required=True)
    args = parser.parse_args()
    if args.action == 'begin':
        print(begin(args.spec, args.run))
    else:
        result = finish(args.run, args.begin_sha256, args.exit_code, args.log)
        print(json.dumps(dict(status=result['status'], changed_inputs=result['changed_inputs'])))
        if result['status'] != 'recorded_success':
            sys.exit(1)


if __name__ == '__main__':
    main()
