"""Prepare a K256 print-only invocation; never launch a compiler or simulator."""
import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import sys

from controller_native_validate import digest
import record_kernel_evidence as evidence


def read_loadpaths(path):
    args = path.read_text().splitlines()
    return evidence.validate_loadpaths(args)


def resolve_module(args, name):
    return evidence.resolve_module(args, 'LadderQuartz.' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='New preparation directory')
    parser.add_argument('--loadpaths', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, action='append', required=True,
                        help='Versioned begin/result directory; repeat for both proof graphs')
    parser.add_argument('--rocq', type=Path, required=True)
    parser.add_argument('--ocamlpath', required=True)
    parser.add_argument('--lock-directory', type=Path, required=True)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[1]
    loadpaths = read_loadpaths(args.loadpaths)
    expected = {}
    records = [evidence.load_evidence(path) for path in args.evidence]
    targets = {}
    for record in records:
        for name, value in record['inventory_before'].items():
            if name in expected and expected[name] != value:
                raise ValueError(f'Conflicting proof inventories: {name}')
            expected[name] = value
        for target, pair in record['spec']['artifacts'].items():
            if target in targets and targets[target] != pair:
                raise ValueError(f'Conflicting target bindings: {target}')
            targets[target] = pair
        if record['spec']['environment']['OCAMLPATH'] != args.ocamlpath:
            raise ValueError('Printer tool environment differs from checked environment')
        if digest(args.rocq) != digest(Path(record['spec']['tools']['compiler'])):
            raise ValueError('Printer compiler differs from recorded tool')
    for record in records:
        for module, checked in record['modules'].items():
            resolved = evidence.resolve_module(loadpaths, module)
            if (str(resolved) not in expected or
                    expected[str(resolved)] != record['inventory_before'][checked]):
                raise ValueError(f'Print overlay changes a checked module: {module}')
    for module in ('sv_printer', 'masked_controller_native_export'):
        artifact = resolve_module(loadpaths, module)
        target = 'LadderQuartz.' + module
        if target not in targets or Path(targets[target]['artifact']).resolve() != artifact:
            raise ValueError(f'Missing or mismatched successful target binding: {target}')
        if expected.get(str(artifact)) != digest(artifact):
            raise ValueError(f'Resolved artifact absent from verified inventories: {artifact}')
        if digest(artifact.with_suffix('.v')) != digest(repo / 'quartz' / (module + '.v')):
            raise ValueError(f'Canonical source differs from checked source: {module}')
    verilator = shutil.which(os.environ.get('VERILATOR', 'verilator'))
    if verilator is None:
        raise ValueError('Set VERILATOR or add verilator to PATH')
    rocq = args.rocq.resolve(strict=True)
    out = args.output.resolve()
    out.mkdir()
    entry = out / 'masked_controller_native_print.v'
    shutil.copy2(repo / 'quartz' / entry.name, entry)
    small = dict(cpu_seconds=90, wall_seconds=120, rss_bytes=2684354560)
    large = dict(cpu_seconds=600, wall_seconds=900, rss_bytes=6442450944)
    config = dict(
        shares=256, adapter=str(repo / 'quartz/controller_native_adapter.py'),
        signature_checker=str(repo / 'quartz/controller_native_signature.py'),
        wrapper=str(repo / 'quartz/masked_controller_rtl_wrapper.sv'),
        bench=str(repo / 'quartz/masked_controller_rtl_smoke.sv'), verilator=verilator,
        proof_inputs=sorted(set(expected) | {str(p.resolve()) for p in
            [*(directory / name for directory in args.evidence
               for name in ('begin.json', 'result.json', 'kernel.log')),
             args.loadpaths, rocq, entry, Path(__file__), Path(evidence.__file__)]}),
        print_command=[str(rocq), 'compile', '-q', '-time', *loadpaths, str(entry)],
        working_directory=str(out), lock_directory=str(args.lock_directory.resolve()),
        environment=dict(OCAMLPATH=args.ocamlpath,
                         **{k: os.environ[k] for k in ('CXX', 'LDFLAGS') if k in os.environ}),
        limits=dict(print=dict(large, log_bytes=536870912), adapt=large, signature_generate=large,
                    signature_compile=small, signature_run=small, elaborate=large, simulate=large),
        gate_notes=dict(launch_authorized=False, prepared_only=True,
                        downstream_limits='Draft: separately authorize actual K256 full simulation',
                        evidence_schema=evidence.SCHEMA, run_ids=[record['run_id'] for record in records],
                        certificate_binding='Trusted build-script status and closure inventories, not authenticated certificates'))
    config_path = out / 'config.json'
    config_path.write_text(json.dumps(config, indent=2) + '\n')
    command = [sys.executable, '-B', str(repo / 'quartz/controller_native_validate.py'),
               str(config_path), str(out / 'print-audit'), '--print-only']
    print('Prepared only; resource authorization is separate. Command:')
    print(shlex.join(command))


if __name__ == '__main__':
    main()
