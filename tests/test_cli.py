"""Workflow integration controls with an isolated, deterministic fake compiler.

These tests exercise orchestration and record validation. The real Lean replay
is a separate check; the fake compiler makes no mathematical claims.
"""
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import audit_library as audit


class WorkflowControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='covering-cli-tests-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / 'project with spaces'
        self.root.mkdir()
        shutil.copy2(ROOT / 'covering', self.root / 'covering')
        shutil.copytree(ROOT / 'scripts', self.root / 'scripts', ignore=shutil.ignore_patterns('__pycache__'))
        modules = {
            'CoveringDesigns.C11_5_2.Stanton': [],
            'CoveringDesigns.C11_5_2': ['CoveringDesigns.C11_5_2.Stanton'],
            'CoveringDesigns.C12_6_3.Structural.Reduction': ['CoveringDesigns.C11_5_2'],
            'CoveringDesigns.C12_6_3': ['CoveringDesigns.C12_6_3.Structural.Reduction'],
            'CoveringDesigns.C13_7_4': ['CoveringDesigns.C12_6_3.Structural.Reduction'],
            'CoveringDesigns': [c['entry'] for c in audit.COMPONENTS.values()],
        }
        for name, imports in modules.items():
            self.write('lean/' + name.replace('.', '/') + '.lean',
                       ''.join('import ' + dep + '\n' for dep in imports))
        for name in ('C11_5_2', 'C12_6_3', 'C13_7_4', 'All'):
            self.write('lean/audits/' + name + '.lean', '-- fixture audit\n')
        self.write('lean/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lean/lakefile.toml', 'name = "covering_designs"\n')
        self.write('lean/lake-manifest.json', json.dumps({'packages': [
            {'name': 'mathlib', 'dir': 'vendor/mathlib', 'configFile': 'lakefile.toml'}]}))
        self.write('lean/vendor/mathlib/lakefile.toml', 'name = "mathlib"\n')
        self.write('lean/vendor/mathlib/.lake/build/lib/lean/Mathlib.olean', 'dependency cache')
        self.write('lean/vendor/dependencies-provenance.json', '{}\n')
        self.outside = Path(self.temporary.name) / 'outside'
        self.outside.mkdir()
        theorems = [name for c in audit.COMPONENTS.values() for name in c['theorems'] + c['milestones']]
        theorems += [audit.explicit_theorem(key) for key in audit.COMPONENTS]
        fake = textwrap.dedent('''\
            #!/usr/bin/env python3
            import hashlib, json, os
            from pathlib import Path
            import sys, time
            args = sys.argv[1:]
            if '--version' in args:
                print('Lean (version 4.34.1, fixture)')
                raise SystemExit(0)
            with Path('invocations.jsonl').open('a') as stream:
                stream.write(json.dumps(args) + '\\n')
            source = args[-1]
            if os.environ.get('FAKE_SLEEP_SOURCE') and source.endswith(os.environ['FAKE_SLEEP_SOURCE']):
                Path('ready.json').write_text(json.dumps({'pid': os.getpid()}))
                time.sleep(30)
            if os.environ.get('FAKE_FAIL_SOURCE') and source.endswith(os.environ['FAKE_FAIL_SOURCE']):
                print('Controlled compiler failure')
                raise SystemExit(17)
            if os.environ.get('FAKE_REMOVE_PIN'):
                Path('lean/lean-toolchain').unlink()
            if '-o' in args:
                path = Path(args[args.index('-o') + 1])
                path.write_bytes(hashlib.sha256(Path(source).read_bytes()).digest())
            else:
                for theorem in THEOREMS:
                    print("'" + theorem + "' depends on axioms: [propext, Classical.choice, Quot.sound]")
            ''').replace('THEOREMS', repr(sorted(set(theorems))))
        self.write('bin/lake', fake)
        (self.root / 'bin/lake').chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'])

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def cli(self, *args, expected=0, env=None):
        result = subprocess.run([sys.executable, str(self.root / 'covering'), *args],
                                cwd=self.outside, env=env or self.env,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
        return result

    def verify(self, *extra, expected=0, env=None):
        return self.cli('verify', '--memory-mib', '256', '--build-timeout', '5',
                        '--audit-timeout', '5', '--json', *extra, expected=expected, env=env)

    def state(self):
        paths = sorted((self.root / 'results/runs').glob('*/state.json'))
        return json.loads(paths[-1].read_text())

    def invocations(self):
        path = self.root / 'invocations.jsonl'
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def test_runs_from_outside_workspace_and_plan_does_not_compile(self):
        doctor = json.loads(self.cli('doctor', '--json').stdout)
        self.assertTrue(doctor['ready'])
        self.assertEqual(doctor['root'], str(self.root.resolve()))
        plan = json.loads(self.cli('plan', '13-7-4', '--json').stdout)
        self.assertEqual(plan['steps'][-1]['name'], 'c13-audit')
        self.assertEqual(self.invocations(), [])
        self.assertFalse((self.root / 'results').exists())



    def test_complete_verify_is_current_and_resume_revalidates_without_compiling(self):
        result = json.loads(self.verify().stdout)
        self.assertEqual(result['verified'], list(audit.COMPONENTS))
        self.assertEqual(self.state()['status'], 'complete')
        status = json.loads(self.cli('status', '--json').stdout)
        self.assertEqual(status['state'], 'verified')
        before = self.invocations()
        self.cli('verify', '--resume', '--json')
        self.assertEqual(before, self.invocations())
        self.cli('audit')

    def test_unguarded_verification_keeps_audits_and_checked_resume(self):
        # This makes any accidental import or execution of the watchdog fail.
        self.write('scripts/run_memory_guard.py', "raise RuntimeError('watchdog must not run')\n")
        self.cli('doctor', '--no-memory-guard')
        self.verify('--no-memory-guard')
        state = self.state()
        self.assertFalse(state['limits']['memory_guard'])
        summary = json.loads((self.root / 'results/library-verification.json').read_text())
        self.assertTrue(summary['no_native_assertions'])
        self.assertTrue(summary['no_admissions_or_custom_mathematical_axioms'])
        for step in state['plan']:
            path = self.root / 'results/runs' / state['run_id'] / ('step-' + step['name'] + '.run.json')
            record = json.loads(path.read_text())
            self.assertIsNone(record['memory_guard_mib'])
            self.assertEqual(record['executed_command'], step['command'])
        before = self.invocations()
        self.cli('verify', '--resume', '--json')
        self.assertEqual(self.invocations(), before)
        self.cli('audit')
        changed_mode = self.cli('verify', '--resume', '--memory-guard', expected=1)
        self.assertIn('differs from the run', changed_mode.stderr)
        # The audit must reject a record claiming a different execution mode.
        record['memory_guard_mib'] = 256
        path.write_text(json.dumps(record))
        self.cli('audit', expected=1)

    def test_unguarded_commands_keep_exit_status_and_timeout_cleanup(self):
        self.write('scripts/run_memory_guard.py', "raise RuntimeError('watchdog must not run')\n")
        self.cli('run', '--name', 'failure', '--no-memory-guard', '--',
                 sys.executable, '-c', 'raise SystemExit(7)', expected=7)
        self.cli('run', '--name', 'timeout', '--no-memory-guard', '--timeout', '0.5', '--',
                 sys.executable, '-c',
                 "from pathlib import Path; import os,time; Path('owned-pid').write_text(str(os.getpid())); time.sleep(30)",
                 expected=124)
        with self.assertRaises(ProcessLookupError):
            os.kill(int((self.root / 'owned-pid').read_text()), 0)
        for path in (self.root / 'results/commands').glob('*/*.run.json'):
            record = json.loads(path.read_text())
            self.assertIsNone(record['memory_guard_mib'])
            self.assertEqual(record['executed_command'], record['command'])

    def test_failed_run_resumes_and_preserves_failed_attempt(self):
        env = dict(self.env, FAKE_FAIL_SOURCE='C13_7_4.lean')
        result = self.verify(expected=17, env=env)
        self.assertIn('Controlled compiler failure', result.stdout)
        state = self.state()
        self.assertEqual(state['status'], 'failed')
        self.assertFalse((self.root / 'results/library-verification.json').exists())
        prior = self.invocations()
        resume = self.cli('verify', '--resume', state['run_id'], '--json')
        self.assertIn('Reused', resume.stderr)
        following = self.invocations()[len(prior):]
        self.assertTrue(following[0][-1].endswith('C13_7_4.lean'))
        logs = list((self.root / 'results/runs' / state['run_id'] / 'attempts').rglob('*.log'))
        self.assertTrue(any('Controlled compiler failure' in p.read_text() for p in logs))

    def test_changed_proof_inputs_and_changed_limits_reject_resume(self):
        self.verify()
        self.cli('verify', '--resume', '--memory-mib', '512', expected=1)
        self.write('lean/CoveringDesigns/C11_5_2/Stanton.lean', '-- changed source\n')
        before = self.invocations()
        result = self.cli('verify', '--resume', '--json', expected=1)
        self.assertIn('Proof inputs changed', result.stdout)
        self.assertEqual(before, self.invocations())

    def test_changed_runner_rejects_resume(self):
        self.verify()
        path = self.root / 'scripts/record_io.py'
        path.write_text(path.read_text() + '\n# modified runner\n')
        result = self.cli('verify', '--resume', '--json', expected=1)
        self.assertIn('Verification scripts changed', result.stdout)

    def test_tampered_compiled_output_rebuilds_the_remaining_plan(self):
        self.verify()
        state = self.state()
        builds = [s for s in state['plan'] if s['kind'] == 'build']
        step = builds[1]
        output = step['command'][step['command'].index('-o') + 1]
        self.write(output, 'corrupt compiled module')
        prior = len(self.invocations())
        self.cli('verify', '--resume', '--json')
        following = self.invocations()[prior:]
        self.assertEqual(following[0], step['command'][1:])
        self.assertEqual(len(following), len(state['plan']) - 1)
        self.cli('audit')

    def test_tampered_log_invalidates_status_and_audit(self):
        self.verify()
        state = self.state()
        log = self.root / 'results/runs' / state['run_id'] / ('step-' + state['plan'][0]['name'] + '.log')
        log.write_text(log.read_text() + 'changed log\n')
        status = json.loads(self.cli('status', '--json').stdout)
        self.assertEqual(status['state'], 'stale')
        self.assertIn('Changed build/audit log', status['reason'])
        self.cli('audit', expected=1)

    def test_new_run_does_not_overwrite_historical_records(self):
        self.verify()
        state = self.state()
        path = self.root / 'results/runs' / state['run_id'] / 'verification.json'
        before = path.read_bytes()
        self.verify()
        self.assertNotEqual(state['run_id'], self.state()['run_id'])
        self.assertEqual(before, path.read_bytes())

    def test_timeout_records_failure_and_cleans_up_the_owned_command(self):
        self.cli('run', '--name', 'timeout', '--timeout', '0.5', '--memory-mib', '256',
                 '--json', '--', sys.executable, '-c',
                 "from pathlib import Path; import os,time; Path('owned-pid').write_text(str(os.getpid())); time.sleep(30)",
                 expected=124)
        pid = int((self.root / 'owned-pid').read_text())
        with self.assertRaises(ProcessLookupError):
            os.kill(pid, 0)
        record = next((self.root / 'results/commands').glob('*/timeout.run.json'))
        self.assertTrue(json.loads(record.read_text())['watchdog_timeout'])

    def test_ctrl_c_saves_interrupted_state_and_cleans_up_then_resumes(self):
        env = dict(self.env, FAKE_SLEEP_SOURCE='Stanton.lean')
        proc = subprocess.Popen([sys.executable, str(self.root / 'covering'), 'verify', '--json',
                                 '--memory-mib', '256'], cwd=self.outside, env=env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            deadline = time.monotonic() + 8
            while not (self.root / 'ready.json').exists() and time.monotonic() < deadline:
                time.sleep(0.02)
            self.assertTrue((self.root / 'ready.json').exists())
            child_pid = json.loads((self.root / 'ready.json').read_text())['pid']
            proc.send_signal(signal.SIGINT)
            stdout, stderr = proc.communicate(timeout=12)
            self.assertEqual(proc.returncode, 130, stdout + stderr)
            self.assertEqual(self.state()['status'], 'interrupted')
            with self.assertRaises(ProcessLookupError):
                os.kill(child_pid, 0)
            self.cli('verify', '--resume', '--json')
            self.cli('audit')
        finally:
            if proc.poll() is None:
                proc.terminate()
                proc.communicate(timeout=12)

    def test_workspace_lock_prevents_two_verifications(self):
        self.write('results/.workflow.lock', '')
        code = "import fcntl,sys,time; f=open(sys.argv[1],'a+'); fcntl.flock(f,fcntl.LOCK_EX); print('ready',flush=True); time.sleep(30)"
        proc = subprocess.Popen([sys.executable, '-c', code, str(self.root / 'results/.workflow.lock')],
                                stdout=subprocess.PIPE, text=True)
        try:
            self.assertEqual(proc.stdout.readline().strip(), 'ready')
            result = self.cli('verify', '--json', expected=1)
            self.assertIn('Workspace is busy', result.stdout)
            self.assertEqual(self.invocations(), [])
        finally:
            proc.terminate()
            proc.wait(timeout=5)
            proc.stdout.close()

    def test_invalid_limits_names_and_missing_commands_do_not_start_work(self):
        for args in [('verify', '--build-timeout', 'nan'), ('verify', '--memory-mib', '0'),
                     ('plan', '--audit-timeout', 'inf')]:
            self.cli(*args, expected=2)
        self.cli('run', '--name', '../escape', '--', 'true', expected=1)
        self.cli('run', '--name', 'missing', expected=1)
        self.assertEqual(self.invocations(), [])

    def test_missing_dependency_fails_before_compilation(self):
        (self.root / 'lean/vendor/mathlib/lakefile.toml').unlink()
        result = self.cli('verify', '--json', expected=1)
        self.assertIn('Prerequisites failed', result.stdout)
        self.assertEqual(self.invocations(), [])

    def test_python_optimization_cannot_disable_record_validation(self):
        result = subprocess.run([sys.executable, '-O', str(self.root / 'covering'), 'verify'],
                                cwd=self.outside, env=self.env, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 2)
        self.assertIn('without Python optimization', result.stderr)
        self.assertEqual(self.invocations(), [])

    def test_lost_proof_input_preserves_a_failed_command_record(self):
        env = dict(self.env, FAKE_REMOVE_PIN='1')
        self.cli('run', '--name', 'lost-input', '--json', '--',
                 'lake', '-d', 'lean', 'env', 'lean', 'lean/audits/All.lean', expected=1, env=env)
        path = next((self.root / 'results/commands').glob('*/lost-input.run.json'))
        record = json.loads(path.read_text())
        self.assertFalse(record['proof_inputs_unchanged'])
        self.assertIn('lean-toolchain', record['proof_input_error'])

    def test_legacy_entry_point_uses_the_same_workflow(self):
        result = subprocess.run([sys.executable, str(self.root / 'scripts/audit_library.py'),
                                 '--verify', '--component', '11-5-2', '--memory-mib', '256'],
                                cwd=self.outside, env=self.env, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.state()['target'], '11-5-2')
        self.cli('audit', '11-5-2')


if __name__ == '__main__':
    unittest.main()
