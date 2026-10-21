"""One entry point for routine covering-design project work."""
import argparse
import json
import math
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
from datetime import datetime, timezone
import uuid

import audit_library as audit
import workflow
from record_io import workspace_lock

ROOT = Path(__file__).resolve().parents[1]


def positive_float(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise argparse.ArgumentTypeError('must be positive and finite')
    return number


def positive_int(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError('must be positive')
    return number


def parser_for_cli():
    parser = argparse.ArgumentParser(prog='covering', description=__doc__,
        epilog='Start with: ./covering doctor, ./covering check, ./covering verify. '
               'All paths and commands are resolved from the project root.')
    commands = parser.add_subparsers(dest='action', required=True)

    def add(name, help_text, target=False):
        command = commands.add_parser(name, help=help_text, description=help_text)
        command.add_argument('--json', action='store_true', help='emit machine-readable output')
        if target:
            command.add_argument('target', nargs='?', choices=workflow.TARGETS, default='all')
        return command

    def guard_option(command, default=True):
        command.add_argument('--memory-guard', action=argparse.BooleanOptionalAction,
                             default=default, help='sample process-group RSS (default: enabled; optional in CI)')

    doctor = add('doctor', 'Check the toolchain, vendored dependencies, caches and optional memory watchdog')
    guard_option(doctor)
    add('status', 'Inspect current verification and the latest run without rebuilding', target=True)
    add('check', 'Check sources, input hashes, explicit covers and generated data without Lean')
    add('audit', 'Validate recorded verification against current inputs without rebuilding', target=True)
    for name in ('plan', 'verify'):
        command = add(name, 'Show the canonical verification plan' if name == 'plan'
                      else 'Compile and audit a component or the whole library', target=True)
        command.add_argument('--workers', type=int, choices=(1, 2),
                             help='concurrent fresh build commands; audits stay serial (fresh default: 2; resume keeps recorded count)')
        command.add_argument('--memory-mib', type=positive_int,
                             help='per-command Lean -M and optional process-group RSS limit; up to two groups (default: 8192 MiB each)')
        guard_option(command, default=None)
        command.add_argument('--build-timeout', type=positive_float,
                             help='time limit per module (default: 180 seconds)')
        command.add_argument('--audit-timeout', type=positive_float,
                             help='time limit per audit (default: 30 seconds)')
        if name == 'verify':
            command.add_argument('--resume', nargs='?', const='latest', metavar='RUN_ID',
                                 help='reuse validated steps from the latest or named run')
    controls = add('controls', 'Run the snapshot, Linux fixture and live memory-watchdog controls')
    guard_option(controls)
    controls.add_argument('suite', nargs='?', choices=('all', 'audit', 'linux', 'memory'), default='all')
    run = add('run', 'Run a custom command with logging, timeout, memory guard and cleanup')
    run.add_argument('--name', required=True, help='a short label for the recorded command')
    run.add_argument('--timeout', type=positive_float, default=180)
    run.add_argument('--memory-mib', type=positive_int, default=8192)
    guard_option(run)
    run.add_argument('command', nargs=argparse.REMAINDER, help='command and arguments after --')
    return parser


def quick_checks():
    from verify_cover import verify
    from generate_gppt_completions import data, production_data

    closures = audit.check_sources()
    audit.check_manifests()
    checks = [
        {'name': 'source boundaries and admissions', 'ok': True,
         'detail': f'{len(set().union(*closures.values()))} proof modules'},
        {'name': 'input manifests', 'ok': True},
    ]
    for name, v, k, t in [('data/ljcr-30.json', 13, 7, 4), ('data/gppt-figure6.json', 12, 6, 3)]:
        result = verify(json.loads(Path(name).read_text())['blocks'], v, k, t)
        assert result['uncovered'] == 0, f'{name}: uncovered subsets'
        checks.append({'name': name, 'ok': True, 'detail': result})
    catalogue = json.loads(Path('data/links-68.json').read_text())
    classes = catalogue['links']
    assert len(classes) == 68, 'Expected 68 catalogue entries'
    for item in classes:
        result = verify(item['blocks'], 12, 6, 3)
        assert result['blocks'] == 15 and result['uncovered'] == 0, 'Invalid catalogue cover'
    checks.append({'name': '68 catalogue covers', 'ok': True})
    generated = production_data(data())
    assert Path('lean/CoveringDesigns/C12_6_3/Structural/CompletionData.lean').read_text() == generated, \
        'CompletionData.lean differs from its deterministic generator'
    checks.append({'name': 'completion data reproducibility', 'ok': True})
    result = subprocess.run([sys.executable, 'scripts/check_audit_controls.py'],
                            capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr
    checks.append({'name': 'snapshot negative controls', 'ok': True,
                   'detail': json.loads(result.stdout)})
    return {'passed': True, 'checks': checks,
            'scope': 'Source and data checks; Lean proof verification is ./covering verify'}


def workspace_busy():
    import fcntl

    path = Path('results/.workflow.lock')
    if not path.exists():
        return False
    with path.open() as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        fcntl.flock(stream, fcntl.LOCK_UN)
    return False


def status_result(target):
    result = workflow.verification_status(target)
    result['workspace_busy'] = workspace_busy()
    state = workflow.latest_run(None if target == 'all' else target)
    if state:
        visible = {k: state.get(k) for k in ('run_id', 'target', 'status', 'current_step', 'updated_utc', 'error')}
        if visible['status'] == 'running' and not result['workspace_busy']:
            visible['status'] = 'interrupted'
        visible['completed_steps'] = len(state['completed'])
        visible['total_steps'] = len(state['plan'])
        visible['state_file'] = f'results/runs/{state["run_id"]}/state.json'
        visible['resume_command'] = f'./covering verify {state["target"]} --resume {state["run_id"]}'
        result['latest_run'] = visible
    return result


def command_run(name, command, timeout, memory_mib, report):
    if not workflow.RUN_ID.fullmatch(name):
        raise ValueError('--name must begin with a letter or digit and contain only letters, digits, ., _ or -')
    if command[:1] == ['--']:
        command = command[1:]
    if not command:
        raise ValueError('A command is required after --')
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ') + '-' + name + '-' + uuid.uuid4().hex[:8]
    directory = Path('results/commands') / run_id
    report(f'Running {shlex.join(command)}\nLog: {directory / (name + ".log")}')
    code, output = workflow.logged_command(command, name, timeout, memory_mib, directory)
    if code:
        log = directory / (name + '.log')
        detail = '\n'.join(log.read_text().splitlines()[-15:]) if log.exists() else output.strip()
        raise workflow.StepFailed(code, f'Command failed (exit {code}). Log: {log}\n{detail}')
    return {'passed': True, 'record': str(directory / (name + '.run.json')),
            'log': str(directory / (name + '.log'))}


def render(action, result):
    if action == 'doctor':
        for check in result['checks']:
            label = 'OK' if check['ok'] else ('FAIL' if check.get('required', True) else 'INFO')
            print(f'{label} {check["name"]}: {check["detail"]}')
        print('Ready for verification.' if result['ready'] else 'Resolve the failed prerequisites before verification.')
    elif action in ('status', 'audit'):
        print(f'{result["target"]}: {result["state"]}')
        if 'record' in result:
            print(f'{result["steps"]} checked steps; record: {result["record"]}')
        if 'reason' in result:
            print(result['reason'])
        if 'next_command' in result:
            print('Next: ' + result['next_command'])
        if 'latest_run' in result:
            run = result['latest_run']
            print(f'Latest run: {run["run_id"]} ({run["status"]}; {run["completed_steps"]}/{run["total_steps"]} steps)')
            if run['current_step']:
                print('Step: ' + run['current_step'])
            if run['status'] in ('failed', 'interrupted'):
                print('Resume: ' + run['resume_command'])
    elif action == 'check':
        for check in result['checks']:
            print('OK ' + check['name'])
        print(result['scope'])
    elif action == 'plan':
        mode = 'enabled' if result['limits']['memory_guard'] else 'disabled'
        print(f'{result["target"]}: {len(result["steps"])} steps; {result["limits"]["workers"]} build worker(s); '
              f'Lean -M{result["limits"]["memory_mib"]}; memory watchdog {mode}')
        for index, step in enumerate(result['steps'], 1):
            print(f'[{index}] ({step["timeout_seconds"]:g}s) {shlex.join(step["command"])}')
    else:
        print(json.dumps(result, indent=2))


def main(argv=None):
    os.chdir(ROOT)
    parser = parser_for_cli()
    args = parser.parse_args(argv)
    if not __debug__:
        parser.error('Run the CLI without Python optimization (-O).')

    def report(message):
        print(message, file=sys.stderr if args.json else sys.stdout, flush=True)

    def interrupted(signum, _frame):
        exc = InterruptedError(f'Interrupted by signal {signum}')
        exc.signum = signum
        raise exc

    previous = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGTERM, signal.SIGHUP)}
    try:
        code = 0
        if args.action == 'doctor':
            result = workflow.doctor(memory_guard=args.memory_guard)
            code = 0 if result['ready'] else 1
        elif args.action in ('status', 'audit'):
            result = status_result(args.target)
            if args.action == 'audit':
                code = 0 if result['state'] == 'verified' else 1
        elif args.action == 'check':
            result = quick_checks()
        elif args.action in ('plan', 'verify'):
            limits = {name: getattr(args, name) for name in workflow.DEFAULT_LIMITS}
            if args.action == 'plan':
                audit.check_sources()
                limits = {k: v if v is not None else workflow.DEFAULT_LIMITS[k] for k, v in limits.items()}
                result = {'target': args.target, 'limits': limits, 'steps': workflow.plan_for(args.target, limits)}
            else:
                result = workflow.run_verification(args.target, limits, args.resume, report)
        elif args.action == 'run':
            with workspace_lock():
                result = command_run(args.name, args.command, args.timeout,
                                     args.memory_mib if args.memory_guard else None, report)
        elif args.action == 'controls':
            suites = {'audit': 'scripts/check_audit_controls.py',
                      'linux': 'lean/pilots/VerificationControls/check_linux_inspector.py',
                      'memory': 'lean/pilots/VerificationControls/check_memory_guard.py'}
            selected = suites if args.suite == 'all' else {args.suite: suites[args.suite]}
            records = {}
            with workspace_lock():
                for name, script in selected.items():
                    records[name] = command_run('controls-' + name, [sys.executable, script], 60,
                                                512 if args.memory_guard else None, report)
            result = {'passed': True, 'controls': records}
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            render(args.action, result)
        return code
    except (KeyboardInterrupt, InterruptedError) as exc:
        report(str(exc) or 'Interrupted; completed verification steps are saved.')
        return 128 + getattr(exc, 'signum', signal.SIGINT)
    except (AssertionError, ValueError, OSError, KeyError, TypeError,
            StopIteration, subprocess.SubprocessError, workflow.StepFailed) as exc:
        if args.json:
            print(json.dumps({'error': str(exc), 'action': args.action}))
        else:
            print(f'covering: {exc}', file=sys.stderr)
        return getattr(exc, 'code', 1)
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


if __name__ == '__main__':
    raise SystemExit(main())
