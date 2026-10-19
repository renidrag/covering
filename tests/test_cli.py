"""Workflow integration controls with an isolated, deterministic fake compiler.

These tests exercise orchestration and record validation. The real Lean replay
is a separate check; the fake compiler makes no mathematical claims.
Per-component contract/axiom combinations live in test_audit_policy.py and use
the production validator directly. End-to-end rejection and record controls
remain here, with no change to the real verification limits or trust checks.
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
import workflow
from lean_inputs import snapshot
from workflow_fixtures import header_graph, reachable, source_headers


class WorkflowFixture:
    whole_library = False

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='covering-cli-tests-')
        self.addCleanup(lambda: self.assertFalse(Path(self.temporary.name).exists()))
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / 'project with spaces'
        self.root.mkdir()
        for path in audit.RUNNER_INPUTS:
            target = self.root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / path, target)
        for name, content in source_headers(whole=self.whole_library).items():
            self.write(name, content)
        for key in audit.COMPONENTS:
            self.write(str(audit.audit_source(key)), '-- fixture audit\n')
        self.write('lean/audits/All.lean', '-- fixture audit\n')
        self.write('lean/lean-toolchain', 'leanprover/lean4:v4.34.1\n')
        self.write('lean/lakefile.toml', 'name = "covering_designs"\n')
        self.write('lean/lake-manifest.json', json.dumps({'packages': [
            {'name': 'mathlib', 'dir': 'vendor/mathlib', 'configFile': 'lakefile.toml'}]}))
        self.write('lean/vendor/mathlib/lakefile.toml', 'name = "mathlib"\n')
        self.write('lean/vendor/mathlib/.lake/build/lib/lean/Mathlib.olean', 'dependency cache')
        self.write('lean/vendor/dependencies-provenance.json', '{}\n')
        self.outside = Path(self.temporary.name) / 'outside'
        self.outside.mkdir()
        audit_theorems = {
            str(audit.audit_source(key)): sorted(set(
                info['theorems'] + info['milestones'] + [audit.explicit_theorem(key)]))
            for key, info in audit.COMPONENTS.items()}
        audit_theorems['lean/audits/All.lean'] = sorted({
            audit.principal_theorem(key) for key in audit.COMPONENTS})
        self.write('audit-theorems.json', json.dumps(audit_theorems))
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
                for theorem in json.loads(Path('audit-theorems.json').read_text())[source]:
                    if theorem == os.environ.get('FAKE_OMIT_THEOREM'):
                        continue
                    axioms = 'propext, Classical.choice, Quot.sound'
                    if theorem == os.environ.get('FAKE_AXIOMS_THEOREM'):
                        axioms = os.environ['FAKE_AXIOMS']
                    print("'" + theorem + "' depends on axioms: [" + axioms + "]")
            ''')
        self.write('bin/lake', fake)
        (self.root / 'bin/lake').chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'])

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def cli(self, *args, expected=0, env=None):
        command = [sys.executable, str(self.root / 'covering'), *args]
        proc = subprocess.Popen(command, cwd=self.outside, env=env or self.env,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, start_new_session=True)
        try:
            # The real graph has more modules than the old synthetic whole
            # library. This harness ceiling is not a performance assertion or a
            # production limit; all per-command watchdogs remain enabled.
            stdout, stderr = proc.communicate(timeout=120 if self.whole_library else 60)
        except BaseException:
            # subprocess.run's timeout kills the CLI before it can clean its
            # detached command groups. Let the real interruption handler run.
            if proc.poll() is None:
                proc.send_signal(signal.SIGINT)
            try:
                proc.communicate(timeout=12)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate(timeout=3)
            raise
        result = subprocess.CompletedProcess(command, proc.returncode, stdout, stderr)
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

    def checked_record(self, target):
        """Validate fresh disk evidence directly after a real CLI operation.

        Source policy already ran in verify/resume. checked_summary checks the
        entire current input snapshot and runner hashes again, then all logs,
        commands, outputs and theorem/axiom evidence. Avoid another global
        policy scan just to repeat that record assertion. CLI audit acceptance,
        stale-input rejection and tampering are exercised separately below.
        """
        previous = Path.cwd()
        try:
            os.chdir(self.root)
            path = workflow.summary_path(target)
            keys = json.loads(path.read_text())['components']
            closures = {key: audit.closure(audit.COMPONENTS[key]['entry']) for key in keys}
            return workflow.checked_summary(path, snapshot(), closures)
        finally:
            os.chdir(previous)


class WorkflowControls(WorkflowFixture, unittest.TestCase):
    def test_runs_from_outside_workspace_and_plan_does_not_compile(self):
        doctor = json.loads(self.cli('doctor', '--json').stdout)
        self.assertTrue(doctor['ready'])
        self.assertEqual(doctor['root'], str(self.root.resolve()))
        plan = json.loads(self.cli('plan', '13-7-4', '--json').stdout)
        self.assertEqual(plan['steps'][-1]['name'], 'c13-audit')
        self.assertEqual(self.invocations(), [])
        self.assertFalse((self.root / 'results').exists())



    def test_commented_imports_preserve_dependency_order_and_recorded_closure(self):
        base = 'CoveringDesigns.Foundations.CommentedBase'
        helper = 'CoveringDesigns.Foundations.CommentedBound'
        self.write('lean/' + base.replace('.', '/') + '.lean',
                   '-- import CoveringDesigns.C13_7_4\n')
        self.write('lean/' + helper.replace('.', '/') + '.lean',
                   'import ' + base + '-- import CoveringDesigns.C11_5_2\n')
        self.write('lean/CoveringDesigns/Schoenheim.lean',
                   '\timport ' + helper + ' \t-- import CoveringDesigns.C12_5_2\r\n'
                   'import ' + base + ' --')
        plan = json.loads(self.cli('plan', 'schoenheim', '--json').stdout)
        self.assertEqual([step['name'] for step in plan['steps']],
                         ['build-' + base, 'build-' + helper,
                          'build-CoveringDesigns.Schoenheim', 'schoenheim-audit'])
        self.verify('schoenheim')
        record = json.loads((self.root / 'results/schoenheim-verification.json').read_text())
        self.assertEqual(record['components']['schoenheim']['source_closure'],
                         sorted('lean/' + module.replace('.', '/') + '.lean'
                                for module in (base, helper, 'CoveringDesigns.Schoenheim')))
        self.checked_record('schoenheim')

    def test_commented_imports_reject_missing_transitive_dependency(self):
        helper = 'CoveringDesigns.Foundations.CommentedBound'
        missing = 'lean/CoveringDesigns/Foundations/Missing.lean'
        self.write('lean/CoveringDesigns/Schoenheim.lean',
                   'import ' + helper + ' -- link bounds\n')
        self.write('lean/' + helper.replace('.', '/') + '.lean',
                   'import CoveringDesigns.Foundations.Missing -- prerequisite\n')
        result = self.cli('plan', 'schoenheim', expected=1)
        self.assertIn('Missing local import: ' + missing, result.stderr)

    def test_header_parser_keeps_transitive_order_closure_and_fingerprints(self):
        base = 'CoveringDesigns.Foundations.HeaderBase'
        helper = 'CoveringDesigns.Foundations.HeaderBound'
        self.write('lean/' + base.replace('.', '/') + '.lean', '-- fixture\n')
        self.write('lean/' + helper.replace('.', '/') + '.lean',
                   'module public/- nested /- comment -/ -/import ' + base)
        self.write('lean/CoveringDesigns/Schoenheim.lean',
                   '/-\nimport CoveringDesigns.C11_5_2\n-/\n'
                   'import Mathlib import ' + helper + '\n'
                   'def text := "\nimport CoveringDesigns.C13_7_4\n"')
        plan = json.loads(self.cli('plan', 'schoenheim', '--json').stdout)
        self.assertEqual([step['name'] for step in plan['steps']],
                         ['build-' + base, 'build-' + helper,
                          'build-CoveringDesigns.Schoenheim', 'schoenheim-audit'])
        self.verify('schoenheim')
        record = json.loads((self.root / 'results/schoenheim-verification.json').read_text())
        self.assertEqual(record['components']['schoenheim']['source_closure'],
                         sorted('lean/' + module.replace('.', '/') + '.lean'
                                for module in (base, helper, 'CoveringDesigns.Schoenheim')))
        self.checked_record('schoenheim')
        self.write('lean/' + base.replace('.', '/') + '.lean', '-- changed input\n')
        self.cli('audit', 'schoenheim', expected=1)

    def test_escaped_paths_and_malformed_imports_fail_before_compilation(self):
        for source in ('import «CoveringDesigns/C11_5_2»', 'import /- unterminated',
                       'import «CoveringDesigns', 'import coveringdesigns.C11_5_2'):
            with self.subTest(source=source):
                self.write('lean/CoveringDesigns/Schoenheim.lean', source)
                result = self.cli('plan', 'schoenheim', expected=1)
                self.assertIn('Cannot audit Lean imports', result.stderr)
                self.assertEqual(self.invocations(), [])

    def test_escaped_exploration_import_is_rejected(self):
        self.write('lean/Explorations/Probe.lean', '-- fixture\n')
        self.write('lean/CoveringDesigns/Schoenheim.lean',
                   'import/- exploratory -/«Explorations».Probe')
        result = self.cli('plan', 'schoenheim', expected=1)
        self.assertIn('Explorations/Probe.lean', result.stderr)

    def test_local_import_aliases_are_rejected(self):
        # Both a case-insensitive filesystem and an explicit symlink can
        # otherwise resolve this spelling to the forbidden C11 component.
        original = self.root / 'lean/CoveringDesigns/C11_5_2.lean'
        alias = original.with_name('c11_5_2.lean')
        if not alias.exists():
            alias.symlink_to(original.name)
        self.write('lean/CoveringDesigns/Schoenheim.lean',
                   'import CoveringDesigns.c11_5_2')
        result = self.cli('plan', 'schoenheim', expected=1)
        self.assertIn('noncanonical local path', result.stderr)

    def test_untracked_local_namespace_cannot_hide_a_dependency(self):
        for path in ('lean/Wrapper.lean', 'lean/.lake/build/lib/lean/Wrapper.olean'):
            with self.subTest(path=path):
                wrapper = self.write(path, 'import CoveringDesigns.C11_5_2')
                self.write('lean/CoveringDesigns/Schoenheim.lean', 'import Wrapper')
                result = self.cli('plan', 'schoenheim', expected=1)
                self.assertIn('project-local imports must use', result.stderr)
                wrapper.unlink()

    def test_general_bound_missing_contract_and_changed_axioms_are_rejected(self):
        principal = audit.principal_theorem('schoenheim')
        explicit = audit.explicit_theorem('schoenheim')
        cases = [
            {'FAKE_OMIT_THEOREM': explicit},
            {'FAKE_AXIOMS_THEOREM': principal, 'FAKE_AXIOMS': 'propext'},
            {'FAKE_AXIOMS_THEOREM': explicit, 'FAKE_AXIOMS': 'propext'},
            {'FAKE_AXIOMS_THEOREM': principal, 'FAKE_AXIOMS': 'propext, sorryAx'},
        ]
        for overrides in cases:
            with self.subTest(overrides=overrides):
                self.verify('schoenheim', expected=1, env=dict(self.env, **overrides))
                self.assertFalse((self.root / 'results/schoenheim-verification.json').exists())


    def test_auxiliary_contract_policy_reaches_records(self):
        # Policy combinations are covered exhaustively without subprocesses.
        # This small real workflow verifies the validator is actually wired
        # into record creation, including its non-principal theorem policy.
        theorem = 'CoveringDesigns.Schoenheim.ceilDiv_le_iff'
        for overrides in (
                {'FAKE_OMIT_THEOREM': theorem},
                {'FAKE_AXIOMS_THEOREM': theorem, 'FAKE_AXIOMS': 'propext, sorryAx'}):
            with self.subTest(overrides=overrides):
                result = self.verify('schoenheim', expected=1, env=dict(self.env, **overrides))
                self.assertIn(theorem, result.stdout)
                self.assertEqual(self.state()['status'], 'failed')
                self.assertFalse((self.root / 'results/schoenheim-verification.json').exists())
        self.verify('schoenheim', env=dict(
            self.env, FAKE_AXIOMS_THEOREM=theorem, FAKE_AXIOMS=''))
        record = json.loads((self.root / 'results/schoenheim-verification.json').read_text())
        self.assertEqual(record['components']['schoenheim']['audited_theorem_axioms'][theorem], [])
        self.checked_record('schoenheim')

    def test_unguarded_verification_keeps_audits_and_checked_resume(self):
        # This makes any accidental import or execution of the watchdog fail.
        self.write('scripts/run_memory_guard.py', "raise RuntimeError('watchdog must not run')\n")
        self.cli('doctor', '--no-memory-guard')
        self.verify('13-7-4', '--no-memory-guard')
        state = self.state()
        self.assertFalse(state['limits']['memory_guard'])
        summary = json.loads((self.root / 'results/c13-structural-verification.json').read_text())
        self.assertTrue(summary['no_native_assertions'])
        self.assertTrue(summary['no_admissions_or_custom_mathematical_axioms'])
        for step in state['plan']:
            path = self.root / 'results/runs' / state['run_id'] / ('step-' + step['name'] + '.run.json')
            record = json.loads(path.read_text())
            self.assertIsNone(record['memory_guard_mib'])
            self.assertEqual(record['executed_command'], step['command'])
        before = self.invocations()
        self.cli('verify', '13-7-4', '--resume', '--json')
        self.assertEqual(self.invocations(), before)
        self.cli('audit', '13-7-4')
        changed_mode = self.cli('verify', '13-7-4', '--resume', '--memory-guard', expected=1)
        self.assertIn('differs from the run', changed_mode.stderr)
        # The audit must reject a record claiming a different execution mode.
        record['memory_guard_mib'] = 256
        path.write_text(json.dumps(record))
        self.cli('audit', '13-7-4', expected=1)

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
        # A transitive plan is sufficient for generic record/recovery controls.
        # Whole-library replay and both guard modes are tested separately.
        env = dict(self.env, FAKE_FAIL_SOURCE='C13_7_4.lean')
        result = self.verify('13-7-4', expected=17, env=env)
        self.assertIn('Controlled compiler failure', result.stdout)
        state = self.state()
        self.assertEqual(state['status'], 'failed')
        self.assertFalse((self.root / 'results/c13-structural-verification.json').exists())
        prior = self.invocations()
        resume = self.cli('verify', '13-7-4', '--resume', state['run_id'], '--json')
        self.assertIn('Reused', resume.stderr)
        following = self.invocations()[len(prior):]
        self.assertTrue(following[0][-1].endswith('C13_7_4.lean'))
        logs = list((self.root / 'results/runs' / state['run_id'] / 'attempts').rglob('*.log'))
        self.assertTrue(any('Controlled compiler failure' in p.read_text() for p in logs))

    def test_changed_proof_inputs_and_changed_limits_reject_resume(self):
        self.verify('13-7-4')
        self.cli('verify', '13-7-4', '--resume', '--memory-mib', '512', expected=1)
        self.write('lean/CoveringDesigns/C11_5_2/Stanton.lean', '-- changed source\n')
        before = self.invocations()
        result = self.cli('verify', '13-7-4', '--resume', '--json', expected=1)
        self.assertIn('Proof inputs changed', result.stdout)
        self.assertEqual(before, self.invocations())

    def test_changed_runner_rejects_resume(self):
        self.verify('13-7-4')
        path = self.root / 'scripts/record_io.py'
        path.write_text(path.read_text() + '\n# modified runner\n')
        result = self.cli('verify', '13-7-4', '--resume', '--json', expected=1)
        self.assertIn('Verification scripts changed', result.stdout)

    def test_tampered_compiled_output_rebuilds_the_remaining_plan(self):
        self.verify('13-7-4')
        state = self.state()
        builds = [s for s in state['plan'] if s['kind'] == 'build']
        step = builds[1]
        output = step['command'][step['command'].index('-o') + 1]
        self.write(output, 'corrupt compiled module')
        prior = len(self.invocations())
        self.cli('verify', '13-7-4', '--resume', '--json')
        following = self.invocations()[prior:]
        self.assertEqual(following[0], step['command'][1:])
        self.assertEqual(len(following), len(state['plan']) - 1)
        self.checked_record('13-7-4')

    def test_tampered_log_invalidates_status_and_audit(self):
        self.verify('13-7-4')
        state = self.state()
        summary = self.root / 'results/c13-structural-verification.json'
        original = summary.read_text()
        record = json.loads(original)
        record['dependency_boundaries_checked'] = False
        summary.write_text(json.dumps(record))
        try:
            result = self.cli('audit', '13-7-4', expected=1)
            self.assertIn('Invalid summary field', result.stdout + result.stderr)
        finally:
            summary.write_text(original)
        log = self.root / 'results/runs' / state['run_id'] / ('step-' + state['plan'][0]['name'] + '.log')
        log.write_text(log.read_text() + 'changed log\n')
        status = json.loads(self.cli('status', '13-7-4', '--json').stdout)
        self.assertEqual(status['state'], 'stale')
        self.assertIn('Changed build/audit log', status['reason'])
        self.cli('audit', '13-7-4', expected=1)

    def test_new_run_does_not_overwrite_historical_records(self):
        self.verify('13-7-4')
        state = self.state()
        path = self.root / 'results/runs' / state['run_id'] / 'verification.json'
        before = path.read_bytes()
        self.verify('13-7-4')
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
        proc = subprocess.Popen([sys.executable, str(self.root / 'covering'), 'verify', '13-7-4', '--json',
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
            self.cli('verify', '13-7-4', '--resume', '--json')
            self.checked_record('13-7-4')
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
        self.checked_record('11-5-2')


class WholeLibraryControls(WorkflowFixture, unittest.TestCase):
    whole_library = True

    def test_complete_verify_is_current_and_resume_revalidates_without_compiling(self):
        result = json.loads(self.verify().stdout)
        self.assertEqual(result['verified'], list(audit.COMPONENTS))
        self.assertEqual(self.state()['status'], 'complete')
        record = json.loads((self.root / 'results/library-verification.json').read_text())
        graph = header_graph(source_headers(whole=True))
        expected_builds = {'lean/' + m.replace('.', '/') + '.lean'
                           for m in reachable(graph, 'CoveringDesigns')}
        compiled = [args[-1] for args in self.invocations() if '-o' in args]
        self.assertEqual(set(compiled), expected_builds)
        self.assertEqual(len(compiled), len(expected_builds))
        audited = [args[-1] for args in self.invocations() if '-o' not in args]
        self.assertEqual(set(audited), {str(audit.audit_source(key)) for key in audit.COMPONENTS}
                         | {'lean/audits/All.lean'})
        self.assertEqual(len(audited), len(audit.COMPONENTS) + 1)
        for key, info in audit.COMPONENTS.items():
            with self.subTest(component=key):
                component = record['components'][key]
                self.assertEqual(component['source_closure'], sorted(
                    'lean/' + m.replace('.', '/') + '.lean' for m in reachable(graph, info['entry'])))
                expected = set(info['theorems'] + info['milestones'] + [audit.explicit_theorem(key)])
                self.assertEqual(set(component['audited_theorem_axioms']), expected)
                for name in expected:
                    self.assertEqual(set(component['audited_theorem_axioms'][name]),
                                     {'propext', 'Classical.choice', 'Quot.sound'})
        status = json.loads(self.cli('status', '--json').stdout)
        self.assertEqual(status['state'], 'verified')
        before = self.invocations()
        self.cli('verify', '--resume', '--json')
        self.assertEqual(before, self.invocations())
        self.cli('audit')
        # Keep the selected-component stale-input scenario on this one complete
        # record; a second build of its entire prerequisite graph adds no check.
        path = self.root / 'lean/CoveringDesigns/TwoKMinusCGeneral/Geometry.lean'
        path.write_text(path.read_text() + '\n-- changed input\n')
        self.cli('audit', 'two-k-minus-c-general', expected=1)

if __name__ == '__main__':
    unittest.main()
