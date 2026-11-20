"""Bounded native-controller integration runner; compilation is not a proof certificate."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import time


def digest(path):
    checksum = hashlib.sha256()
    with path.open('rb') as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b''):
            checksum.update(chunk)
    return checksum.hexdigest()


def coverage(text, k):
    rows = re.findall(r'^PASS K=(\d+) full_runs=(\d+) edges=(\d+) observations=(\d+) '
                      r'canonical_words=(\d+)$', text, re.M)
    if len(rows) != 1:
        raise ValueError('Missing or ambiguous controller coverage line')
    actual, runs, edges, observations, words = map(int, rows[0])
    if (actual != k or runs != 4 or edges < 4 * 8680 or observations != edges + 1
            or words != observations * 282 * k):
        raise ValueError('Controller coverage mismatch')
    required = ('PASS full packed HW coverage; branching/power oracle;',
                'PASS synchronous reset/idle, ignored busy starts, done refresh/retention, '
                'current-state gating')
    if any(line not in text for line in required):
        raise ValueError('Missing controller behavior checks')
    return dict(shares=k, full_runs=runs, edges=edges, observations=observations,
                canonical_words=words)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('config', type=Path, help='Explicit printer command, inputs and resource budgets JSON')
    parser.add_argument('output', type=Path, help='New audit directory; must not already exist')
    parser.add_argument('--signature-only', action='store_true', help='Stop after emitted-type width checks')
    parser.add_argument('--print-only', action='store_true', help='Stop after bounded native printing')
    args = parser.parse_args()
    cfg = json.loads(args.config.read_text())
    k = cfg['shares']
    if k not in (2, 4, 256):
        parser.error('Supported validation configurations: 2, 4, 256')
    stages = ('print', 'adapt', 'signature_generate', 'signature_compile', 'signature_run',
              'elaborate', 'simulate')
    for stage in stages:
        if any(cfg['limits'][stage][key] <= 0 for key in ('cpu_seconds', 'wall_seconds', 'rss_bytes')):
            parser.error('Every stage requires explicit positive resource limits')
        if 'log_bytes' in cfg['limits'][stage] and cfg['limits'][stage]['log_bytes'] <= 0:
            parser.error('Log byte limits must be positive')
    paths = {key: Path(cfg[key]).resolve(strict=True)
             for key in ('adapter', 'signature_checker', 'wrapper', 'bench', 'verilator')}
    inputs = [*paths.values(), *(Path(p).resolve(strict=True) for p in cfg['proof_inputs'])]
    hashes = {str(p): digest(p) for p in inputs}
    if not cfg['proof_inputs'] or not cfg['print_command']:
        parser.error('Explicit proof inputs and printer command are required')
    out = args.output.resolve()
    out.mkdir()
    shutil.copy2(args.config, out / 'configuration.json')
    for key in ('adapter', 'signature_checker', 'wrapper', 'bench'):
        shutil.copy2(paths[key], out / paths[key].name)
    env = dict(os.environ, **cfg.get('environment', {}))
    compiler_flags = ['-MAKEFLAGS', f'CXX={env["CXX"]} LINK={env["CXX"]}'] if env.get('CXX') else []
    lock = Path(cfg['lock_directory'])
    report = dict(status='incomplete', shares=k, input_sha256=hashes, stages=[],
                  runner_sha256=digest(Path(__file__)), proof_certification='external, not inferred')
    report['cpu_limit_scope'] = 'per process; wall and sampled RSS guards cover owned process group'

    def interrupted(signum, frame):
        raise InterruptedError(f'Interrupted by signal {signum}')

    signal.signal(signal.SIGTERM, interrupted)

    def save():
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')

    def run(stage, command):
        limits = cfg['limits'][stage]
        record = dict(stage=stage, command=command, limits=limits, peak_group_rss_bytes=0)
        report['stages'].append(record)
        save()
        def cpu_limit():
            resource.setrlimit(resource.RLIMIT_CPU,
                               (limits['cpu_seconds'], limits['cpu_seconds'] + 1))
            if 'log_bytes' in limits:
                resource.setrlimit(resource.RLIMIT_FSIZE, (limits['log_bytes'], limits['log_bytes']))
        started = time.monotonic()
        record.update(start_utc=datetime.now(timezone.utc).isoformat(), start_monotonic=started)
        child = None
        log_path = out / (stage + '.log')
        try:
            if 'log_bytes' in limits:
                free = shutil.disk_usage(out).free
                record['disk_free_before_bytes'] = free
                if free < 2 * limits['log_bytes']:
                    raise RuntimeError('Insufficient free disk for bounded stage output')
            # Fail before spawning work if process-group monitoring is unavailable.
            subprocess.check_output(['ps', '-Ao', 'pgid=,rss='], text=True, timeout=10)
            with (out / (stage + '.log')).open('w') as log:
                child = subprocess.Popen(command, cwd=cfg['working_directory'], env=env,
                                         stdout=log, stderr=subprocess.STDOUT,
                                         start_new_session=True, preexec_fn=cpu_limit)
                record['pid'] = child.pid
                record['pgid'] = child.pid
                record['spawned'] = True
                save()
                while child.poll() is None:
                    rows = subprocess.check_output(['ps', '-Ao', 'pgid=,rss='], text=True, timeout=10)
                    rss = sum(int(row.split()[1]) * 1024 for row in rows.splitlines()
                              if row.split()[0] == str(child.pid))
                    record['peak_group_rss_bytes'] = max(record['peak_group_rss_bytes'], rss)
                    elapsed = time.monotonic() - started
                    if 'log_bytes' in limits and log_path.stat().st_size >= limits['log_bytes']:
                        record['termination_reason'] = 'output_limit'
                        os.killpg(child.pid, signal.SIGKILL)
                        break
                    if rss > limits['rss_bytes'] or elapsed > limits['wall_seconds']:
                        record['termination_reason'] = 'rss_limit' if rss > limits['rss_bytes'] else 'wall_limit'
                        os.killpg(child.pid, signal.SIGKILL)
                        break
                    time.sleep(0.2)
                code = child.wait()
        except BaseException as error:
            record['error'] = repr(error)
            raise
        finally:
            if child is not None:
                # No owned compiler/simulator descendants survive failure or interruption.
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                record['exit_code'] = child.wait()
                if record['exit_code'] == -signal.SIGXCPU:
                    record['termination_reason'] = 'cpu_limit'
                if record['exit_code']:
                    record.setdefault('error', f'Child exited with code {record["exit_code"]}')
            else:
                record['exit_code'] = None
                record['spawned'] = False
            record['log_bytes'] = log_path.stat().st_size if log_path.exists() else 0
            if ('log_bytes' in limits and record['log_bytes'] >= limits['log_bytes']
                    or record['exit_code'] == -signal.SIGXFSZ):
                record['termination_reason'] = 'output_limit'
            ended = time.monotonic()
            record.update(end_utc=datetime.now(timezone.utc).isoformat(), end_monotonic=ended,
                          wall_seconds=ended - started)
            save()
        if code or record.get('termination_reason') == 'output_limit':
            raise RuntimeError(f'{stage} failed: {code}')

    lock.mkdir()
    try:
        run('print', cfg['print_command'])
        if args.print_only:
            if any(digest(Path(path)) != value for path, value in hashes.items()):
                raise RuntimeError('Input changed during printing')
            report['status'] = 'print_pass_only'
            return
        run('adapt', [sys.executable, str(out / paths['adapter'].name), str(out / 'print.log'),
                      str(out), '--shares', str(k)])
        run('signature_generate', [sys.executable, str(out / paths['signature_checker'].name),
                                   str(out / 'controller.sv'), str(out), '--shares', str(k)])
        run('signature_compile', [str(paths['verilator']), '--binary', '--timing', '-Wno-fatal',
                                  '--top-module', 'controller_signature_probe', '-j', '1',
                                  '--Mdir', str(out / 'signature_obj'), *compiler_flags,
                                  str(out / 'signature.sv')])
        run('signature_run', [str(out / 'signature_obj/Vcontroller_signature_probe')])
        signature = json.loads((out / 'signature.json').read_text())
        expected = (f'PASS signature K={k} request={signature["expected_request_bits"]} '
                    f'response={signature["expected_response_bits"]}')
        if (out / 'signature_run.log').read_text().splitlines().count(expected) != 1:
            raise RuntimeError('Missing or ambiguous native signature width result')
        report['signature_check'] = dict(
            status='pass', evidence=signature,
            execution=dict(compile_exit_code=0, run_exit_code=0,
                           run_log='signature_run.log',
                           run_log_sha256=digest(out / 'signature_run.log'),
                           compile_log='signature_compile.log',
                           compile_log_sha256=digest(out / 'signature_compile.log')))
        if args.signature_only:
            if any(digest(Path(path)) != value for path, value in hashes.items()):
                raise RuntimeError('Input changed during signature validation')
            report['status'] = 'signature_pass_only'
            return
        entry = f'cycle{k}'
        run('elaborate', [str(paths['verilator']), '--binary', '--timing', '-Wno-fatal',
                          '--top-module', 'masked_controller_rtl_smoke', '-j', '1',
                          *compiler_flags,
                          '--Mdir', str(out / 'obj'), f'-DQUARTZ_SHARES={k}',
                          f'-DQUARTZ_ENTRY={entry}', str(out / 'controller.sv'),
                          str(out / paths['wrapper'].name), str(out / paths['bench'].name)])
        run('simulate', [str(out / 'obj/Vmasked_controller_rtl_smoke')])
        report['coverage'] = coverage((out / 'simulate.log').read_text(), k)
        if any(digest(Path(path)) != value for path, value in hashes.items()):
            raise RuntimeError('Input changed during validation')
        report['status'] = 'native_simulation_pass'
    except BaseException as error:
        report['status'] = 'failed'
        report['error'] = str(error)
        raise
    finally:
        try:
            artifacts = [out / name for name in ('controller.raw.sv', 'controller.sv', 'emission.json',
                         'configuration.json', paths['wrapper'].name, paths['bench'].name,
                         paths['adapter'].name, paths['signature_checker'].name,
                         'signature.sv', 'signature.json', 'signature_obj/Vcontroller_signature_probe',
                         'obj/Vmasked_controller_rtl_smoke')]
            artifacts.extend(out.glob('*.log'))
            report['output_sha256'] = {str(p.relative_to(out)): digest(p)
                                       for p in artifacts if p.is_file()}
            save()
        finally:
            lock.rmdir()


if __name__ == '__main__':
    main()
