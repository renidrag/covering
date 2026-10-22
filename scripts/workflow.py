"""Durable dependency-ordered verification with one or two build workers."""
from contextlib import contextmanager
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid

import audit_library as audit
from lean_inputs import changed_paths, sha, snapshot, validate_snapshot
from record_io import workspace_lock, write_json

DEFAULT_LIMITS = {'memory_mib': 8192, 'build_timeout': 180.0, 'audit_timeout': 30.0,
                  'memory_guard': True, 'workers': 2}
TARGETS = ('all', *audit.COMPONENTS)
RUN_ID = re.compile(r'[A-Za-z0-9][A-Za-z0-9._-]*')


def now():
    return datetime.now(timezone.utc).isoformat()


def keys_for(target):
    return tuple(audit.COMPONENTS) if target == 'all' else (target,)


def summary_path(target):
    if target == 'all':
        return Path('results/library-verification.json')
    if target == '13-7-4':
        return Path('results/c13-structural-verification.json')
    if 'summary_path' in audit.COMPONENTS[target]:
        return Path(audit.COMPONENTS[target]['summary_path'])
    return Path(f'results/c{target.split("-")[0]}-verification.json')


def runner_hashes():
    return {str(p): sha(p) for p in audit.RUNNER_INPUTS}


def plan_for(target, limits):
    return [{'name': name, 'kind': kind, 'command': command,
             'timeout_seconds': limits['build_timeout' if kind == 'build' else 'audit_timeout']}
            for name, (kind, command) in audit.verification_plan(keys_for(target), limits['memory_mib']).items()]


def doctor(*, memory_guard=True):
    checks = []

    def add(name, ok, detail, required=True):
        checks.append({'name': name, 'ok': bool(ok), 'detail': detail, 'required': required})

    add('python', sys.version_info >= (3, 14) and __debug__,
        f'{sys.version.split()[0]}; Python 3.14+ without -O is required')
    try:
        from compression import zstd
        add('zstd support', True, f'standard-library compression.zstd {zstd.zstd_version}')
    except ImportError:
        add('zstd support', False,
            'Install Python 3.14+ with compression.zstd; compressed provenance checks are required')
    add('platform', sys.platform == 'darwin' or sys.platform.startswith('linux'), sys.platform)
    if memory_guard:
        try:
            from run_memory_guard import make_inspector
            inspector = make_inspector()
            add('memory watchdog', True, inspector.backend)
        except Exception as exc:
            add('memory watchdog', False, str(exc))
    else:
        add('memory watchdog', True, 'disabled by request')
    try:
        manifest = json.loads(Path('lean/lake-manifest.json').read_text())
        for package in manifest['packages']:
            directory = Path('lean') / package['dir']
            config = directory / package['configFile']
            add('dependency ' + package['name'], config.is_file(), str(config))
            cache = directory / '.lake/build/lib/lean'
            add('cache ' + package['name'], cache.is_dir() and next(cache.rglob('*.olean'), None) is not None,
                str(cache), required=package['name'] != 'Cli')
        add('dependency provenance', Path('lean/vendor/dependencies-provenance.json').is_file(),
            'lean/vendor/dependencies-provenance.json')
    except (OSError, ValueError, KeyError, TypeError) as exc:
        add('dependency manifest', False, str(exc))
    lake = shutil.which('lake')
    add('lake', lake is not None, lake or 'Install Lake/elan and put lake on PATH')
    version = None
    if lake and all(c['ok'] for c in checks if c['name'].startswith('dependency ')):
        try:
            result = subprocess.run(['lake', '-d', 'lean', 'env', 'lean', '--version'],
                                    capture_output=True, text=True, timeout=30)
            version = result.stdout.strip()
            pin = Path('lean/lean-toolchain').read_text().strip().split(':')[-1].removeprefix('v')
            add('lean toolchain', result.returncode == 0 and
                re.search(r'\bversion ' + re.escape(pin) + r'(?:,|\s|\))', version) is not None,
                version or result.stderr.strip())
        except (OSError, subprocess.TimeoutExpired) as exc:
            add('lean toolchain', False, str(exc))
    return {'ready': all(c['ok'] for c in checks if c['required']), 'root': str(Path.cwd()),
            'lean_version': version, 'checks': checks}


def latest_run(target=None):
    for path in sorted(Path('results/runs').glob('*/state.json'), reverse=True):
        try:
            state = json.loads(path.read_text())
            if target is None or state['target'] == target:
                return state
        except (OSError, ValueError, KeyError, TypeError):
            continue
    return None


def checked_summary(path, current, closures):
    """Check proof records and logs, rather than trusting a stored success flag."""
    record = json.loads(path.read_text())
    validate_snapshot(record, current)
    assert record['verification_script_sha256'] == runner_hashes(), 'Verification scripts changed'
    keys = tuple(record['components'])
    assert keys and set(keys) <= set(audit.COMPONENTS), 'Unexpected recorded components'
    prefix = record.get('run_prefix')
    if prefix is None:
        prefix = 'library-current' if len(keys) == len(audit.COMPONENTS) else 'c13-current'
    memory_mib = record['limits']['memory_mib']
    memory_guard = record['limits']['memory_guard']
    assert type(memory_mib) is int and memory_mib > 0, 'Invalid recorded Lean memory limit'
    assert type(memory_guard) is bool, 'Invalid recorded memory guard mode'
    workers = record['limits'].get('workers', 1)
    assert type(workers) is int and workers in (1, 2), 'Invalid recorded build worker count'
    plan = audit.verification_plan(keys, memory_mib)
    for name in plan:
        step_record = json.loads(audit.record_path(prefix, name).read_text())
        assert step_record.get('verification_workers') == workers, 'Changed recorded build worker count'
    expected = audit.verification_record(keys, prefix, plan, current, closures, record['lean_version'],
                                         memory_guard=memory_guard)
    for field in ('components', 'verification_runs', 'no_admissions_or_custom_mathematical_axioms',
                  'no_native_assertions', 'dependency_boundaries_checked', 'proof_inputs_unchanged'):
        assert record.get(field) == expected[field], f'Invalid summary field: {field}'
    return record


def verification_status(target='all'):
    paths = [summary_path(target)]
    if target != 'all':
        paths.append(summary_path('all'))
    errors = []
    try:
        closures = audit.check_sources()
        audit.check_manifests()
        current = snapshot()
    except (AssertionError, ValueError, OSError, KeyError, TypeError) as exc:
        return {'target': target, 'state': 'invalid', 'reason': str(exc),
                'next_command': './covering check'}
    for path in paths:
        if not path.is_file():
            continue
        try:
            record = checked_summary(path, current, closures)
            assert set(keys_for(target)) <= set(record['components']), 'Target not in verification record'
            return {'target': target, 'state': 'verified', 'record': str(path),
                    'recorded_utc': record['recorded_utc'], 'lean_version': record['lean_version'],
                    'steps': len(record['verification_runs'])}
        except (AssertionError, ValueError, OSError, KeyError, TypeError, StopIteration) as exc:
            errors.append(f'{path}: {exc}')
    return {'target': target, 'state': 'stale' if errors else 'unverified',
            'reason': '; '.join(errors) if errors else 'No recorded verification for this target',
            'next_command': './covering verify' + ('' if target == 'all' else ' ' + target)}


INTERRUPTION_SIGNALS = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)


@contextmanager
def deferred_interruptions():
    """Register a spawned child before Python can unwind on a signal.

    Handlers, not signal masks: the logger/Lean child must not inherit blocked
    signals. The original handler is invoked after the protected operation.
    """
    received = []
    previous = {sig: signal.signal(sig, lambda signum, frame: received.append((signum, frame)))
                for sig in INTERRUPTION_SIGNALS}
    try:
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        if received:
            signum, frame = received[0]
            handler = previous[signum]
            if callable(handler):
                handler(signum, frame)
            elif handler != signal.SIG_IGN:
                raise InterruptedError(f'Interrupted by signal {signum}')


@contextmanager
def ignored_interruptions():
    """Finish cleanup and terminal records despite repeated cancellation."""
    previous = {sig: signal.signal(sig, signal.SIG_IGN) for sig in INTERRUPTION_SIGNALS}
    try:
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


class LoggedCommand:
    """One owned logger process; output is a file, never a blocking pipe."""

    def __init__(self, command, name, timeout, memory_mib, output_dir):
        runner = [sys.executable, 'scripts/run_logged.py', '--name', name,
                  '--timeout', str(timeout), '--output-dir', str(output_dir)]
        if memory_mib is not None:
            runner.extend(['--memory-mib', str(memory_mib)])
        runner.extend(['--', *command])
        self.output = tempfile.TemporaryFile(mode='w+t')
        try:
            self.proc = subprocess.Popen(runner, stdout=self.output, stderr=subprocess.STDOUT,
                                         text=True, start_new_session=True)
        except BaseException:
            self.output.close()
            raise

    def poll(self):
        return self.proc.poll()

    def result(self):
        self.proc.wait()
        self.output.seek(0)
        return self.proc.returncode, self.output.read()

    def close(self):
        self.output.close()

    def signal(self, signum):
        try:
            os.killpg(self.proc.pid, signum)
        except ProcessLookupError:
            pass


def stop_logged_commands(jobs):
    """Signal every logger first; one cleanup error must not strand its peer."""
    errors = []
    with ignored_interruptions():
        running = []
        for job in jobs:
            try:
                if job.poll() is None:
                    running.append(job)
            except OSError as exc:
                errors.append(str(exc))
                running.append(job)
        for job in running:
            try:
                job.signal(signal.SIGTERM)
            except OSError as exc:
                errors.append(str(exc))
        deadline = time.monotonic() + 9
        for job in running:
            try:
                job.proc.wait(timeout=max(0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                pass
            except OSError as exc:
                errors.append(str(exc))
        remaining = []
        for job in running:
            try:
                if job.poll() is None:
                    remaining.append(job)
            except OSError as exc:
                errors.append(str(exc))
                remaining.append(job)
        for job in remaining:
            try:
                job.signal(signal.SIGKILL)
            except OSError as exc:
                errors.append(str(exc))
        for job in remaining:
            try:
                job.proc.wait(timeout=3)
            except (OSError, subprocess.TimeoutExpired) as exc:
                errors.append(str(exc))
        for job in jobs:
            try:
                job.close()
            except OSError as exc:
                errors.append(str(exc))
    if errors:
        raise ValueError('Logger cleanup reported errors: ' + '; '.join(errors))


def logged_command(command, name, timeout, memory_mib, output_dir):
    jobs = []
    try:
        with deferred_interruptions():
            job = LoggedCommand(command, name, timeout, memory_mib, output_dir)
            jobs.append(job)
        return job.result()
    finally:
        stop_logged_commands(jobs)


def build_dependencies(plan):
    """Derive direct prerequisites without changing canonical plan identities."""
    graph = audit.SourceGraph()
    positions = {step['name']: index for index, step in enumerate(plan) if step['kind'] == 'build'}
    dependencies = {}
    for name, index in positions.items():
        module = name.removeprefix('build-')
        dependencies[name] = ['build-' + dep for dep in graph.imports(module)]
        assert all(dep in positions and positions[dep] < index for dep in dependencies[name]), \
            f'Build dependency missing or out of order: {name}'
    return dependencies


def execute_plan(plan, dependencies, workers, completed, start, finish, changed):
    """A single coordinator owns launches, validation and durable state.

    Ready builds are dispatched in canonical order. Audits form a serial
    barrier after all builds, and no work is dispatched after an observed error.
    """
    assert type(workers) is int and workers in (1, 2), 'Expected one or two build workers'
    completed = set(completed)
    pending = [step for step in plan if step['name'] not in completed]
    builds = set(dependencies)
    active = {}
    outcomes = {step['name']: 'reused' if step['name'] in completed else 'pending' for step in plan}

    def update():
        changed([step['name'] for step in plan if step['name'] in active],
                [step['name'] for step in plan if step['name'] in completed], dict(outcomes))

    try:
        while pending or active:
            # Drain every observed completion before dispatch. In particular a
            # failed peer cannot be hidden by an earlier successful completion.
            for name, (step, job) in list(active.items()):
                if job.poll() is not None:
                    try:
                        finish(step, job)
                    except BaseException:
                        outcomes[name] = 'failed'
                        raise
                    completed.add(name)
                    outcomes[name] = 'verified'
                    del active[name]
                    job.close()
                    update()
            ready = [step for step in pending if step['kind'] == 'build'
                     and set(dependencies[step['name']]) <= completed]
            if builds <= completed and not active:
                ready = pending[:1]  # audits remain serial
            for step in ready[:workers - len(active)]:
                name = step['name']
                try:
                    with deferred_interruptions():
                        job = start(step)
                        active[name] = (step, job)
                        pending.remove(step)
                        outcomes[name] = 'running'
                        update()
                except (KeyboardInterrupt, InterruptedError):
                    raise
                except BaseException:
                    outcomes[name] = 'failed'
                    raise
            if pending and not active:
                raise ValueError('Verification scheduler has no ready step')
            if active:
                time.sleep(0.01)
    finally:
        with ignored_interruptions():
            # No terminal state or lock release until every owned logger has
            # been drained, or cleanup errors have been explicitly reported.
            cleanup_error = None
            try:
                stop_logged_commands([job for _, job in active.values()])
            except Exception as exc:
                cleanup_error = exc
            for name in active:
                if outcomes[name] == 'running':
                    outcomes[name] = 'cleanup-failed' if cleanup_error else 'cancelled'
            for step in pending:
                if outcomes[step['name']] == 'pending':
                    outcomes[step['name']] = 'not-run'
            if not cleanup_error:
                active.clear()
            update()
            if cleanup_error:
                raise cleanup_error


class StepFailed(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


def run_verification(target, limits, resume=None, report=print):
    if not __debug__:
        raise ValueError('Run verification without Python optimization (-O).')
    with workspace_lock():
        requested_limits = limits
        state = None
        if resume:
            if resume == 'latest':
                state = latest_run(target)
                if state is None:
                    raise ValueError(f'No {target} run to resume. Start ./covering verify {target}.')
            else:
                if not RUN_ID.fullmatch(resume):
                    raise ValueError('Invalid run ID; use the ID printed by ./covering status.')
                state = json.loads((Path('results/runs') / resume / 'state.json').read_text())
            # Runs without worker metadata predate parallel scheduling and are
            # serial, independently of the default for fresh local runs.
            recorded_limits = {**DEFAULT_LIMITS, 'workers': 1, **state['limits']}
            for name, value in requested_limits.items():
                if value is not None and value != recorded_limits[name]:
                    raise ValueError(f'--{name.replace("_", "-")} differs from the run; start a new verification')
            limits = recorded_limits
        else:
            limits = {name: requested_limits.get(name) if requested_limits.get(name) is not None else value
                      for name, value in DEFAULT_LIMITS.items()}
        assert type(limits['workers']) is int and limits['workers'] in (1, 2), 'Expected one or two build workers'
        # This serial Lake invocation also loads/warm-validates configuration
        # caches before concurrent lake env commands (Lake owns cache locks).
        environment = doctor(memory_guard=limits['memory_guard'])
        if not environment['ready']:
            failures = '; '.join(c['name'] + ': ' + c['detail'] for c in environment['checks'] if c['required'] and not c['ok'])
            raise ValueError('Prerequisites failed: ' + failures + '. Use ./covering doctor.')
        closures = audit.check_sources()
        audit.check_manifests()
        current = snapshot()
        scripts = runner_hashes()
        if resume:
            assert state['target'] == target, f'Run belongs to {state["target"]}, not {target}'
            assert not changed_paths(state['proof_input_sha256'], current), 'Proof inputs changed; start a new verification'
            assert state['verification_script_sha256'] == scripts, 'Verification scripts changed; start a new verification'
            assert state['lean_version'] == environment['lean_version'], 'Lean version changed; start a new verification'
            assert state['plan'] == plan_for(target, limits), 'Verification plan changed; start a new verification'
            assert state['build_dependencies'] == build_dependencies(state['plan']), 'Build dependencies changed'
            report(f'Resuming {state["run_id"]}')
        else:
            run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ') + '-' + uuid.uuid4().hex[:8]
            state = {'schema_version': 2, 'run_id': run_id, 'target': target,
                     'started_utc': now(), 'limits': limits, 'plan': plan_for(target, limits),
                     'proof_input_sha256': current, 'verification_script_sha256': scripts,
                     'lean_version': environment['lean_version'], 'completed': []}
            state['build_dependencies'] = build_dependencies(state['plan'])
            report(f'Run {run_id}')
        directory = Path('results/runs') / state['run_id']
        prefix = str(directory.relative_to('results') / 'step')
        state_path = directory / 'state.json'

        def save(status, **values):
            state.update(status=status, updated_utc=now(), **values)
            write_json(state_path, state)

        save('running', pid=os.getpid(), current_step=None, active_steps=[], error=None, completed=[])
        try:
            # Preserve the conservative existing resume rule: reuse only the
            # validated canonical prefix, then freshly rebuild the entire tail.
            if resume:
                for step in state['plan']:
                    name, kind, command = (step[k] for k in ('name', 'kind', 'command'))
                    try:
                        audit.successful_run(prefix, name, kind, command, current,
                                             memory_guard=limits['memory_guard'])
                        prior = json.loads(audit.record_path(prefix, name).read_text())
                        assert prior.get('verification_workers') == limits['workers']
                    except (AssertionError, ValueError, OSError, KeyError, TypeError, StopIteration):
                        break
                    state['completed'].append(name)
                    save('running')
                    report(f'Reused {name}')
            positions = {step['name']: index for index, step in enumerate(state['plan'], 1)}

            def start(step):
                name, kind, command = (step[k] for k in ('name', 'kind', 'command'))
                if kind == 'build':
                    Path(command[command.index('-o') + 1]).parent.mkdir(parents=True, exist_ok=True)
                old_files = [directory / ('step-' + name + suffix) for suffix in ('.log', '.run.json')]
                if any(p.exists() for p in old_files):
                    attempt = directory / 'attempts' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
                    attempt.mkdir(parents=True)
                    for path in old_files:
                        if path.exists():
                            shutil.copy2(path, attempt / path.name)
                report(f'[{positions[name]}/{len(state["plan"])}] Checking {name}')
                return LoggedCommand(command, 'step-' + name, step['timeout_seconds'],
                                     limits['memory_mib'] if limits['memory_guard'] else None, directory)

            def finish(step, job):
                name, kind, command = (step[k] for k in ('name', 'kind', 'command'))
                code, output = job.result()
                if code:
                    log = directory / ('step-' + name + '.log')
                    detail = '\n'.join(log.read_text().splitlines()[-15:]) if log.exists() else output.strip()
                    raise StepFailed(code, f'{name} failed (exit {code}). Log: {log}\n{detail}')
                path = audit.record_path(prefix, name)
                record = json.loads(path.read_text())
                if kind == 'build':
                    artifact = Path(command[command.index('-o') + 1])
                    record['output_sha256'] = {str(artifact): sha(artifact)}
                record['verification_workers'] = limits['workers']
                write_json(path, record)
                audit.successful_run(prefix, name, kind, command, current,
                                     memory_guard=limits['memory_guard'])
                report(f'[{positions[name]}/{len(state["plan"])}] Checked {name} ({record["elapsed_seconds"]:.2f}s)')

            def changed(active, completed, outcomes):
                save('running', current_step=active[0] if active else None,
                     active_steps=active, completed=completed, step_outcomes=outcomes)

            execute_plan(state['plan'], state['build_dependencies'], limits['workers'],
                         state['completed'], start, finish, changed)
            assert not changed_paths(current, snapshot()), 'Proof inputs changed during verification'
            assert scripts == runner_hashes(), 'Verification scripts changed during verification'
            plan = {s['name']: (s['kind'], s['command']) for s in state['plan']}
            record = audit.verification_record(keys_for(target), prefix, plan, current, closures,
                                               environment['lean_version'], memory_guard=limits['memory_guard'])
            assert scripts == runner_hashes(), 'Verification scripts changed while recording'
            record.update(run_id=state['run_id'], run_prefix=prefix, target=target, limits=limits)
            write_json(directory / 'verification.json', record)
            write_json(summary_path(target), record)
            save('complete', current_step=None, record=str(directory / 'verification.json'))
            return {'verified': list(record['components']), 'run_id': state['run_id'],
                    'record': str(summary_path(target)), 'run_record': str(directory / 'verification.json'),
                    'steps': len(state['plan'])}
        except (KeyboardInterrupt, InterruptedError) as exc:
            with ignored_interruptions():
                save('interrupted', error=str(exc) or 'Interrupted by user')
                report(f'Resume with ./covering verify {target} --resume {state["run_id"]}')
            raise
        except Exception as exc:
            with ignored_interruptions():
                save('failed', error=str(exc))
                report(f'Resume with ./covering verify {target} --resume {state["run_id"]}')
            raise
