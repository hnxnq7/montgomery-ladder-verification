import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch, MagicMock

import controller_native_signature as signature
import controller_native_validate as runner
import prepare_masked_controller_export as prepare
import record_kernel_evidence as evidence


FIXTURE = '''typedef bit[9:0] request_t;
typedef bit[4:0] response_t;
function automatic response_t cycle256 (
  input request_t arg);
  cycle256 = '0;
endfunction
'''


class SignatureTests(unittest.TestCase):
    def test_exact_types_and_formal_widths(self):
        probe, evidence = signature.generate(FIXTURE, 256)
        self.assertEqual(evidence['expected_request_bits'], 53458218)
        self.assertEqual(evidence['expected_response_bits'], 18474257)
        self.assertEqual(evidence['state_bits'], 18408976)
        self.assertEqual(evidence['randomness_bits'], 35048730)
        self.assertIn('typedef request_t actual_request_t;', probe)
        self.assertIn('typedef response_t actual_response_t;', probe)
        self.assertTrue(probe.startswith(FIXTURE[:FIXTURE.index('function')]))
        self.assertNotIn('cycle256 =', probe)
        self.assertIn('$bits(actual_request_t) != 53458218', probe)
        self.assertEqual(evidence['status'], 'generated_only_not_executed')

    def test_wrong_width_is_not_python_certified(self):
        probe, _ = signature.generate(FIXTURE, 256)
        self.assertIn('typedef bit[9:0] request_t;', probe)
        self.assertIn('$fatal(1, "Native request width mismatch")', probe)

    def test_reject_bad_signatures(self):
        for text in (FIXTURE.replace('cycle256', 'other'), FIXTURE + FIXTURE,
                     FIXTURE.replace('cycle256 (', 'bad-name ('),
                     FIXTURE.replace('input request_t arg', 'output request_t arg')):
            with self.subTest(text=text), self.assertRaises(ValueError):
                signature.generate(text, 256)

    def test_nested_types_preserved(self):
        text = FIXTURE.replace('response_t cycle256', 'Pair#(bit[5:0], bit[3:0])::t cycle256')
        _, evidence = signature.generate(text, 256)
        self.assertEqual(evidence['return_type'], 'Pair#(bit[5:0], bit[3:0])::t')


class PreparationTests(unittest.TestCase):
    def test_loadpaths_preserve_empty_namespace_and_late_overlay(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            early, late = root / 'early', root / 'late'
            early.mkdir()
            late.mkdir()
            for directory in (early, late):
                (directory / 'sv_printer.vo').write_bytes(b'fixture')
            paths = root / 'loadpaths.txt'
            paths.write_text(f'-Q\n{root}\n\n-Q\n{early}\nLadderQuartz\n-Q\n{late}\nLadderQuartz\n')
            args = prepare.read_loadpaths(paths)
            self.assertEqual(args[2], '')
            self.assertEqual(prepare.resolve_module(args, 'sv_printer'), (late / 'sv_printer.vo').resolve())
            with self.assertRaises(ValueError):
                prepare.resolve_module(args, 'missing')

    def test_reject_unsupported_or_relative_loadpaths(self):
        with tempfile.TemporaryDirectory() as folder:
            paths = Path(folder) / 'loadpaths.txt'
            for text in ('-Q\nrelative\nLadderQuartz\n', '-Q\n/incomplete\n', '-I\n/tmp\nBad\n'):
                paths.write_text(text)
                with self.subTest(text=text), self.assertRaises(ValueError):
                    prepare.read_loadpaths(paths)


class PreparationGateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        self.repo = self.root / 'repo'
        self.quartz = self.repo / 'quartz'
        self.quartz.mkdir(parents=True)
        self.project = self.root / 'checked'
        self.project.mkdir()
        self.helper = self.quartz / 'prepare_masked_controller_export.py'
        self.helper.write_text('fixture helper')
        (self.quartz / 'masked_controller_native_print.v').write_text('fixture entry')
        inventory = {}
        for name in ('sv_printer', 'masked_controller_native_export'):
            for suffix in ('.v', '.vo'):
                file = self.project / (name + suffix)
                file.write_text(name + suffix)
                inventory[str(file)] = runner.digest(file)
            (self.quartz / (name + '.v')).write_text(name + '.v')
        self.rocq = self.root / 'rocq'
        self.rocq.write_text('fixture tool')
        inventory[str(self.rocq)] = runner.digest(self.rocq)
        self.loadpaths = self.root / 'loadpaths.txt'
        self.loadpaths.write_text(f'-Q\n{self.project}\nLadderQuartz\n')
        self.output = self.root / 'prepared'
        self.spec = self.root / 'spec.json'
        targets = ['LadderQuartz.' + name for name in ('sv_printer', 'masked_controller_native_export')]
        paths = prepare.read_loadpaths(self.loadpaths)
        spec = dict(schema=evidence.SCHEMA, targets=targets, loadpaths=paths,
                    command=[str(self.rocq), '-o', '-m', *paths, *targets],
                    tools=dict(compiler=str(self.rocq), checker=str(self.rocq)),
                    environment=dict(OCAMLPATH=str(self.root / 'plugins')), inventory=list(inventory),
                    artifacts={target: dict(source=str(self.project / (target.split('.')[-1] + '.v')),
                                            artifact=str(self.project / (target.split('.')[-1] + '.vo')))
                               for target in targets})
        self.spec.write_text(json.dumps(spec))
        self.run = self.root / 'evidence'
        receipt = evidence.begin(self.spec, self.run)
        log = self.root / 'kernel-output.log'
        log.write_text('Synthetic unit-test log, not a Rocq execution')
        evidence.finish(self.run, receipt, 0, log)
        self.result = self.run / 'result.json'

    def invoke(self, extra=()):
        argv = ['prepare', str(self.output), '--loadpaths', str(self.loadpaths),
                '--evidence', str(self.run),
                '--rocq', str(self.rocq), '--ocamlpath', str(self.root / 'plugins'),
                '--lock-directory', str(self.root / 'lock'), *extra]
        with patch.object(sys, 'argv', argv), patch.object(prepare, '__file__', str(self.helper)), \
                patch.object(prepare.shutil, 'which', return_value=str(self.rocq)), \
                patch.object(subprocess, 'Popen', side_effect=AssertionError('Preparation launched a child')), \
                patch('sys.stdout', new_callable=io.StringIO) as output:
            prepare.main()
            return output.getvalue()

    def test_preparation_is_print_only_and_never_launches(self):
        output = self.invoke()
        config = json.loads((self.output / 'config.json').read_text())
        self.assertEqual(config['shares'], 256)
        self.assertFalse(config['gate_notes']['launch_authorized'])
        self.assertTrue(config['gate_notes']['prepared_only'])
        self.assertTrue(output.rstrip().endswith('--print-only'))
        self.assertNotIn('--signature-only', output)
        self.assertFalse((self.output / 'print-audit').exists())
        self.assertEqual(config['print_command'][-1], str(self.output / 'masked_controller_native_print.v'))

    def test_reject_missing_module(self):
        missing = self.project / 'sv_printer.vo'
        missing.unlink()
        with self.assertRaisesRegex(ValueError, 'Checked input changed'):
            self.invoke()

    def test_reject_uninventoried_module(self):
        overlay = self.root / 'overlay'
        overlay.mkdir()
        (overlay / 'sv_printer.vo').write_text('unrecorded artifact')
        self.loadpaths.write_text(self.loadpaths.read_text() + f'-Q\n{overlay}\nLadderQuartz\n')
        with self.assertRaisesRegex(ValueError, 'Print overlay changes'):
            self.invoke()

    def test_reject_modified_canonical_source(self):
        (self.quartz / 'sv_printer.v').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Canonical source differs'):
            self.invoke()

    def test_reject_modified_proof_input(self):
        self.rocq.write_text('changed')
        with self.assertRaisesRegex(ValueError, 'Checked input changed'):
            self.invoke()

    def test_reject_unsuccessful_kernel_result(self):
        original = json.loads(self.result.read_text())
        for result in (dict(exit_code=1, inputs_unchanged=True), dict(exit_code=0, inputs_unchanged=False)):
            self.result.write_text(json.dumps(dict(original, **result)))
            with self.subTest(result=result), self.assertRaisesRegex(ValueError, 'Kernel check not successful'):
                self.invoke()

    def test_reject_conflicting_manifests(self):
        result = json.loads(self.result.read_text())
        result['inventory_after'][str(self.rocq)] = '0' * 64
        self.result.write_text(json.dumps(result))
        with self.assertRaisesRegex(ValueError, 'Mismatched before/after'):
            self.invoke()


class EvidenceRecorderTests(unittest.TestCase):
    setUp = PreparationGateTests.setUp

    def pending(self):
        run = self.root / 'pending'
        return run, evidence.begin(self.spec, run), self.root / 'kernel-output.log'

    def test_reject_missing_begin(self):
        with self.assertRaises(FileNotFoundError):
            evidence.finish(self.root / 'absent', '0' * 64, 0, self.root / 'kernel-output.log')

    def test_reject_overwrite(self):
        with self.assertRaises(ValueError):
            evidence.finish(self.run, runner.digest(self.run / 'begin.json'), 0,
                            self.root / 'kernel-output.log')
        with self.assertRaises(FileExistsError):
            evidence.begin(self.spec, self.run)

    def test_preserve_nonzero_result_and_log(self):
        run, receipt, log = self.pending()
        result = evidence.finish(run, receipt, 7, log)
        self.assertEqual(result['status'], 'recorded_failure')
        self.assertEqual(result['exit_code'], 7)
        self.assertEqual((run / 'kernel.log').read_bytes(), log.read_bytes())
        with self.assertRaisesRegex(ValueError, 'not successful'):
            evidence.load_evidence(run)

    def test_preserve_changed_inputs_as_failure(self):
        run, receipt, log = self.pending()
        self.rocq.write_text('changed tool')
        result = evidence.finish(run, receipt, 0, log)
        self.assertEqual(result['status'], 'recorded_failure')
        self.assertIn(str(self.rocq), result['changed_inputs'])

    def test_changed_command_spec_records_failure(self):
        run, receipt, log = self.pending()
        spec = json.loads(self.spec.read_text())
        spec['command'].append('-norec')
        self.spec.write_text(json.dumps(spec))
        result = evidence.finish(run, receipt, 0, log)
        self.assertIn(str(self.spec), result['changed_inputs'])
        self.assertEqual(result['status'], 'recorded_failure')

    def test_reject_tampered_begin_receipt(self):
        run, receipt, log = self.pending()
        with (run / 'begin.json').open('a') as output:
            output.write('\n')
        with self.assertRaisesRegex(ValueError, 'hash mismatch'):
            evidence.finish(run, receipt, 0, log)
        self.assertFalse((run / 'result.json').exists())

    def test_reject_swapped_results(self):
        run, receipt, log = self.pending()
        evidence.finish(run, receipt, 0, log)
        (run / 'result.json').write_bytes(self.result.read_bytes())
        with self.assertRaisesRegex(ValueError, 'Mismatched begin/result'):
            evidence.load_evidence(run)

    def test_reject_unknown_schema_and_changed_log(self):
        result = json.loads(self.result.read_text())
        self.result.write_text(json.dumps(dict(result, schema='future-unknown')))
        with self.assertRaisesRegex(ValueError, 'Unknown evidence'):
            evidence.load_evidence(self.run)
        self.result.write_text(json.dumps(result))
        (self.run / 'kernel.log').write_text('changed log')
        with self.assertRaisesRegex(ValueError, 'Changed kernel log'):
            evidence.load_evidence(self.run)

    def test_reject_partial_recursive_command(self):
        spec = json.loads(self.spec.read_text())
        spec['command'].insert(1, '-norec')
        self.spec.write_text(json.dumps(spec))
        with self.assertRaisesRegex(ValueError, 'full recursive'):
            evidence.begin(self.spec, self.root / 'invalid')

    def test_reject_uninventoried_visible_module(self):
        (self.project / 'hidden.vo').write_bytes(b'unrecorded')
        with self.assertRaisesRegex(ValueError, 'Visible module absent'):
            evidence.begin(self.spec, self.root / 'invalid')

    def test_prepare_rejects_unrelated_successful_target(self):
        spec = json.loads(self.spec.read_text())
        target = 'LadderQuartz.unrelated'
        for suffix in ('.v', '.vo'):
            path = self.project / ('unrelated' + suffix)
            path.write_text('fixture')
            spec['inventory'].append(str(path))
        spec['targets'] = [target]
        spec['artifacts'] = {target: dict(source=str(self.project / 'unrelated.v'),
                                        artifact=str(self.project / 'unrelated.vo'))}
        spec['command'] = [str(self.rocq), '-o', '-m', *spec['loadpaths'], target]
        self.spec.write_text(json.dumps(spec))
        run, receipt, log = self.pending()
        evidence.finish(run, receipt, 0, log)
        self.run = run
        with self.assertRaisesRegex(ValueError, 'Missing or mismatched successful target'):
            PreparationGateTests.invoke(self)


class RunnerTests(unittest.TestCase):
    def test_coverage_requires_complete_counts(self):
        valid = (
            f'PASS K=256 full_runs=4 edges=34720 observations=34721 canonical_words={34721 * 282 * 256}\n'
            'PASS full packed HW coverage; branching/power oracle; coordinates=1 refreshed_groups=1\n'
            'PASS synchronous reset/idle, ignored busy starts, done refresh/retention, current-state gating\n')
        self.assertEqual(runner.coverage(valid, 256)['full_runs'], 4)
        for bad in (valid.replace('full_runs=4 ', ''), valid.replace('observations=34721 ', ''),
                    valid.replace('full_runs=4', 'full_runs=3'),
                    valid.replace('observations=34721', 'observations=34720')):
            with self.subTest(text=bad), self.assertRaises(ValueError):
                runner.coverage(bad, 256)

    def test_streaming_digest_matches_sha256(self):
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'artifact'
            for data in (b'', b'Quartz', bytes(range(256)) * 8193):
                with self.subTest(size=len(data)):
                    path.write_bytes(data)
                    with patch.object(Path, 'read_bytes', side_effect=AssertionError('Whole-file read')):
                        self.assertEqual(runner.digest(path), hashlib.sha256(data).hexdigest())

    def invoke_failure(self, monitor, popen, log_bytes=None):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            keys = ('adapter', 'signature_checker', 'wrapper', 'bench', 'verilator')
            files = {}
            for key in keys:
                path = root / key
                path.write_text(key)
                files[key] = str(path)
            stages = ('print', 'adapt', 'signature_generate', 'signature_compile', 'signature_run',
                      'elaborate', 'simulate')
            cfg = dict(files, shares=256, proof_inputs=[files['wrapper']], print_command=['fake'],
                       working_directory=folder, lock_directory=str(root / 'lock'),
                       limits={s: dict(cpu_seconds=1, wall_seconds=1, rss_bytes=1000) for s in stages})
            if log_bytes is not None:
                cfg['limits']['print']['log_bytes'] = log_bytes
            config = root / 'config.json'
            config.write_text(json.dumps(cfg))
            out = root / 'audit'
            with patch.object(sys, 'argv', ['runner', str(config), str(out)]), \
                    patch.object(subprocess, 'check_output', side_effect=monitor), \
                    patch.object(subprocess, 'Popen', popen), \
                    patch.object(runner.os, 'killpg') as kill:
                with self.assertRaises((OSError, RuntimeError)):
                    runner.main()
            report = json.loads((out / 'result.json').read_text())
            self.assertFalse((root / 'lock').exists())
            self.assertEqual(report['status'], 'failed')
            self.assertIn('wrapper', report['output_sha256'])
            for stage in report['stages']:
                for field in ('exit_code', 'wall_seconds', 'peak_group_rss_bytes'):
                    self.assertIn(field, stage)
            return report, kill.call_count

    def test_output_limit_rejects_even_successful_exit(self):
        child = MagicMock(pid=12345)
        child.poll.return_value = 0
        child.wait.return_value = 0
        def spawn(*args, **kwargs):
            kwargs['stdout'].write('x' * 16)
            kwargs['stdout'].flush()
            return child
        report, _ = self.invoke_failure(['12345 1\n'], MagicMock(side_effect=spawn), log_bytes=16)
        self.assertEqual(len(report['stages']), 1)
        self.assertEqual(report['stages'][0]['termination_reason'], 'output_limit')
        self.assertEqual(report['stages'][0]['log_bytes'], 16)

    def test_disk_preflight_failure_does_not_spawn(self):
        popen = MagicMock()
        with patch.object(runner.shutil, 'disk_usage', return_value=MagicMock(free=15)):
            report, _ = self.invoke_failure([], popen, log_bytes=16)
        popen.assert_not_called()
        self.assertIn('Insufficient free disk', report['stages'][0]['error'])

    def test_preflight_failure_does_not_spawn(self):
        popen = MagicMock()
        report, kills = self.invoke_failure(OSError('ps unavailable'), popen)
        popen.assert_not_called()
        self.assertFalse(report['stages'][0]['spawned'])
        self.assertIsNone(report['stages'][0]['exit_code'])
        self.assertEqual(kills, 0)

    def test_monitor_failure_reaps_child_and_records_metrics(self):
        child = MagicMock(pid=12345)
        child.poll.return_value = None
        child.wait.return_value = -9
        report, kills = self.invoke_failure(['12345 1\n', OSError('ps failed')],
                                           MagicMock(return_value=child))
        self.assertEqual(report['stages'][0]['exit_code'], -9)
        self.assertIn('ps failed', report['stages'][0]['error'])
        self.assertEqual(kills, 1)

    def test_adapter_is_a_separately_monitored_stage(self):
        child = MagicMock(pid=12345)
        child.poll.return_value = 0
        child.wait.return_value = 0
        report, _ = self.invoke_failure(['12345 1\n', OSError('adapter preflight failed')],
                                       MagicMock(return_value=child))
        self.assertEqual([s['stage'] for s in report['stages']], ['print', 'adapt'])
        self.assertIn('cpu_seconds', report['stages'][1]['limits'])


@unittest.skipUnless(os.environ.get('QUARTZ_SIGNATURE_SV_AUDIT'), 'SV fixture execution requires explicit slot')
class SignatureExecutionTests(unittest.TestCase):
    def test_positive_and_assertion_negatives(self):
        root = Path(os.environ['QUARTZ_SIGNATURE_SV_AUDIT']).resolve()
        root.mkdir()
        scripts = Path(__file__).resolve().parent
        repo = Path(os.environ.get('QUARTZ_ROOT', Path(__file__).resolve().parents[1])).resolve()
        verilator = shutil.which(os.environ.get('VERILATOR', 'verilator'))
        self.assertIsNotNone(verilator, 'Set VERILATOR or add verilator to PATH for SV fixtures')
        compiler_environment = {key: os.environ[key] for key in ('CXX', 'LDFLAGS') if key in os.environ}
        fixtures = (('positive', 53458218, 18474257, None),
                    ('negative_request', 53458217, 18474257, 'Native request width mismatch'),
                    ('negative_response', 53458218, 18474256, 'Native response width mismatch'))
        for name, request_bits, response_bits, expected_error in fixtures:
            folder = root / name
            folder.mkdir()
            source = f'''class Pair #(parameter type A, parameter type B);
  typedef struct packed {{ A fst; B snd; }} t;
endclass
function automatic Pair#(bit[18408975:0], bit[{response_bits - 18408976 - 1}:0])::t cycle256 (
  input Pair#(bit[18408975:0], bit[{request_bits - 18408976 - 1}:0])::t arg);
  cycle256 = '0;
endfunction
'''
            printer = folder / 'printer.txt'
            printer.write_text('= "' + source.replace('"', '""') + '" : string\n')
            stages = ('print', 'adapt', 'signature_generate', 'signature_compile', 'signature_run',
                      'elaborate', 'simulate')
            cfg = dict(shares=256, adapter=str(scripts / 'controller_native_adapter.py'),
                       signature_checker=str(scripts / 'controller_native_signature.py'),
                       wrapper=str(repo / 'quartz/masked_controller_rtl_wrapper.sv'),
                       bench=str(repo / 'quartz/masked_controller_rtl_smoke.sv'),
                       verilator=verilator, proof_inputs=[str(printer)],
                       print_command=['/bin/cat', str(printer)], working_directory=str(folder),
                       lock_directory=str(repo / '.deps/quartz-masked-arithmetic/.masked-build-lock'),
                       environment=compiler_environment,
                       limits={s: dict(cpu_seconds=90, wall_seconds=120, rss_bytes=2684354560)
                               for s in stages})
            config = folder / 'config.json'
            config.write_text(json.dumps(cfg, indent=2))
            with (folder / 'runner.log').open('w') as log:
                completed = subprocess.run([sys.executable, str(scripts / 'controller_native_validate.py'),
                                            str(config), str(folder / 'audit'), '--signature-only'],
                                           stdout=log, stderr=subprocess.STDOUT, timeout=650)
            audit = folder / 'audit'
            report = json.loads((audit / 'result.json').read_text())
            records = {s['stage']: s for s in report['stages']}
            self.assertEqual(records['signature_compile']['exit_code'], 0, (folder / 'runner.log').read_text())
            self.assertEqual(set(records), set(stages[:5]))
            runtime = (audit / 'signature_run.log').read_text()
            if name == 'positive':
                self.assertEqual(completed.returncode, 0)
                self.assertEqual(report['status'], 'signature_pass_only')
                self.assertIn('PASS signature K=256 request=53458218 response=18474257', runtime)
            else:
                self.assertNotEqual(completed.returncode, 0)
                self.assertNotEqual(records['signature_run']['exit_code'], 0)
                self.assertIn(expected_error, runtime)
                self.assertNotIn('PASS signature', runtime)


if __name__ == '__main__':
    unittest.main()
