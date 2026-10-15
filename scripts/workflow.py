"""Durable serial verification built on the project's existing trust checks."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import uuid

import audit_library as audit
from lean_inputs import changed_paths, sha, snapshot, validate_snapshot
from record_io import workspace_lock, write_json

DEFAULT_LIMITS = {'memory_mib': 8192, 'build_timeout': 180.0, 'audit_timeout': 30.0,
                  'memory_guard': True}
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

    add('python', sys.version_info >= (3, 10) and __debug__,
        f'{sys.version.split()[0]}; Python 3.10+ without -O is required')
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
    plan = audit.verification_plan(keys, memory_mib)
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


def logged_command(command, name, timeout, memory_mib, output_dir):
    runner = [sys.executable, 'scripts/run_logged.py', '--name', name,
              '--timeout', str(timeout), '--output-dir', str(output_dir)]
    if memory_mib is not None:
        runner.extend(['--memory-mib', str(memory_mib)])
    runner.extend(['--', *command])
    proc = subprocess.Popen(runner, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            text=True, start_new_session=True)
    try:
        output, _ = proc.communicate()
    except BaseException:
        # run_logged handles TERM and cleans up the owned command group.
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.communicate(timeout=9)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate(timeout=3)
        raise
    return proc.returncode, output


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
            for name, value in requested_limits.items():
                if value is not None and value != state['limits'].get(name, DEFAULT_LIMITS[name]):
                    raise ValueError(f'--{name.replace("_", "-")} differs from the run; start a new verification')
            limits = {'memory_guard': True, **state['limits']}
        else:
            limits = {name: requested_limits.get(name) if requested_limits.get(name) is not None else value
                      for name, value in DEFAULT_LIMITS.items()}
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
            report(f'Resuming {state["run_id"]}')
        else:
            run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ') + '-' + uuid.uuid4().hex[:8]
            state = {'schema_version': 1, 'run_id': run_id, 'target': target,
                     'started_utc': now(), 'limits': limits, 'plan': plan_for(target, limits),
                     'proof_input_sha256': current, 'verification_script_sha256': scripts,
                     'lean_version': environment['lean_version'], 'completed': []}
            report(f'Run {run_id}')
        directory = Path('results/runs') / state['run_id']
        prefix = str(directory.relative_to('results') / 'step')
        state_path = directory / 'state.json'

        def save(status, **values):
            state.update(status=status, updated_utc=now(), **values)
            write_json(state_path, state)

        save('running', pid=os.getpid(), current_step=None, error=None, completed=[])
        rebuild_tail = not bool(resume)
        try:
            for index, step in enumerate(state['plan'], 1):
                name, kind, command = (step[k] for k in ('name', 'kind', 'command'))
                save('running', current_step=name)
                if not rebuild_tail:
                    try:
                        audit.successful_run(prefix, name, kind, command, current,
                                     memory_guard=limits['memory_guard'])
                    except (AssertionError, ValueError, OSError, KeyError, TypeError, StopIteration):
                        rebuild_tail = True
                    else:
                        state['completed'].append(name)
                        save('running')
                        report(f'[{index}/{len(state["plan"])}] Reused {name}')
                        continue
                if kind == 'build':
                    Path(command[command.index('-o') + 1]).parent.mkdir(parents=True, exist_ok=True)
                old_files = [directory / ('step-' + name + suffix) for suffix in ('.log', '.run.json')]
                if any(p.exists() for p in old_files):
                    attempt = directory / 'attempts' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
                    attempt.mkdir(parents=True)
                    for path in old_files:
                        if path.exists():
                            shutil.copy2(path, attempt / path.name)
                report(f'[{index}/{len(state["plan"])}] Checking {name}')
                code, output = logged_command(command, 'step-' + name, step['timeout_seconds'],
                                              limits['memory_mib'] if limits['memory_guard'] else None, directory)
                if code:
                    log = directory / ('step-' + name + '.log')
                    detail = '\n'.join(log.read_text().splitlines()[-15:]) if log.exists() else output.strip()
                    raise StepFailed(code, f'{name} failed (exit {code}). Log: {log}\n{detail}')
                path = audit.record_path(prefix, name)
                record = json.loads(path.read_text())
                if kind == 'build':
                    artifact = Path(command[command.index('-o') + 1])
                    record['output_sha256'] = {str(artifact): sha(artifact)}
                    write_json(path, record)
                audit.successful_run(prefix, name, kind, command, current,
                                     memory_guard=limits['memory_guard'])
                state['completed'].append(name)
                save('running')
                report(f'[{index}/{len(state["plan"])}] Checked {name} ({record["elapsed_seconds"]:.2f}s)')
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
            save('interrupted', error=str(exc) or 'Interrupted by user')
            report(f'Resume with ./covering verify {target} --resume {state["run_id"]}')
            raise
        except Exception as exc:
            save('failed', error=str(exc))
            report(f'Resume with ./covering verify {target} --resume {state["run_id"]}')
            raise
