"""Bounded controls: exit status, aggregate RSS, isolation, and cleanup."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

sys.path.insert(0, str(Path('scripts').resolve()))
import run_memory_guard as guard

PILOT = Path('lean/pilots/VerificationControls')
OUT = PILOT / 'MemoryGuardControls'
OUT.mkdir(exist_ok=True)
tag = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')
inspector = guard.make_inspector()
records = []
owned_groups = set()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def summary(output):
    return json.loads(next(line[len('memory_guard_result '):]
                           for line in output.splitlines() if line.startswith('memory_guard_result ')))


def absent(group):
    owned_groups.add(group)
    deadline = time.monotonic() + 2
    while inspector.members(group) and time.monotonic() < deadline:
        time.sleep(0.02)
    assert not inspector.members(group), f'Owned group {group} remains after cleanup'
    owned_groups.discard(group)


def command(name, *, limit=256, children=1, child_mib=0, seconds=0.15, extra=()):
    state = OUT / f'{tag}-{name}.json'
    cmd = [sys.executable, 'scripts/run_memory_guard.py', '--mib', str(limit),
           sys.executable, str(PILOT / 'memory_guard_workload.py'),
           '--children', str(children), '--child-mib', str(child_mib),
           '--seconds', str(seconds), '--state', str(state), *extra]
    return cmd, state


def run(name, cmd, expected, state):
    started = time.monotonic()
    result = subprocess.run(cmd, capture_output=True, text=True, timeout=8)
    log = OUT / f'{tag}-{name}.log'
    log.write_text(result.stdout + result.stderr)
    assert result.returncode == expected, (name, result.returncode, log.read_text())
    info = summary(result.stdout)
    absent(info['owned_group'])
    records.append({'name': name, 'command': cmd, 'returncode': result.returncode,
                    'elapsed_seconds': time.monotonic() - started,
                    'log': str(log), 'log_sha256': digest(log),
                    'state': str(state), 'summary': info})
    return info


control = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(20)'],
                           start_new_session=True)
try:
    cmd, state = command('normal', child_mib=16, extra=('--exit-code', '7'))
    info = run('normal', cmd, 7, state)
    assert info['outcome'] == 'exit' and info['peak_group_members'] >= 2
    assert 0 < info['observed_peak_group_rss_bytes'] < 256 * 1024**2

    cmd, state = command('aggregate', limit=128, children=2, child_mib=64, seconds=8)
    info = run('aggregate', cmd, 137, state)
    assert info['outcome'] == 'memory_threshold'
    assert info['observed_peak_group_rss_bytes'] > 128 * 1024**2
    assert info['observed_largest_process_rss_bytes'] < 128 * 1024**2
    assert info['peak_group_members'] == 3
    assert control.poll() is None, 'The unrelated controlled process was affected'

    cmd, state = command('churn', children=0, extra=('--churn', '16'))
    info = run('churn', cmd, 0, state)
    assert info['outcome'] == 'exit'

    cmd, state = command('normal-orphan', seconds=8, extra=('--detach',))
    info = run('normal-orphan', cmd, 0, state)
    assert info['outcome'] == 'exit'

    cmd, state = command('inspection-failure', seconds=8)
    injected = [sys.executable, str(PILOT / 'memory_guard_failure.py'), str(state), *cmd[2:]]
    info = run('inspection-failure', injected, 125, state)
    assert info['outcome'] == 'watchdog_error'

    cmd, state = command('timeout', seconds=8)
    name = 'memory-guard-timeout-' + tag
    logged = [sys.executable, 'scripts/run_logged.py', '--name', name, '--timeout', '0.5', *cmd]
    started = time.monotonic()
    result = subprocess.run(logged, capture_output=True, text=True, timeout=8)
    assert result.returncode == 124, result.stdout + result.stderr
    run_record = Path('results', name + '.run.json')
    data = json.loads(run_record.read_text())
    assert data['watchdog_timeout']
    log = Path('results', name + '.log')
    info = summary(log.read_text())
    assert info['outcome'] == 'signal' and info['returncode'] == 128 + signal.SIGTERM
    absent(info['owned_group'])
    records.append({'name': 'run_logged-timeout-cleanup', 'command': logged,
                    'returncode': result.returncode, 'elapsed_seconds': time.monotonic() - started,
                    'run_record': str(run_record), 'run_record_sha256': digest(run_record),
                    'log': str(log), 'log_sha256': digest(log), 'state': str(state), 'summary': info})
    assert control.poll() is None, 'The unrelated controlled process was affected'
finally:
    for group in owned_groups:
        guard.signal_group(group, signal.SIGKILL)
    guard.signal_group(control.pid, signal.SIGKILL)
    control.wait(timeout=2)

sources = ['scripts/run_memory_guard.py', str(PILOT / 'check_memory_guard.py'),
           str(PILOT / 'memory_guard_failure.py'), str(PILOT / 'memory_guard_workload.py')]
assessment = {'recorded_utc': datetime.now(timezone.utc).isoformat(),
              'platform': sys.platform, 'inspection_backend': inspector.backend,
              'source_sha256': {p: digest(p) for p in sources},
              'tests': records, 'unrelated_control_survived': True,
              'scope': 'Sampled owned-process-group RSS watchdog; not a hard, system-wide, or process-tree allocation cap.'}
target = Path('results', 'memory-guard-controls-' + tag + '.json')
target.write_text(json.dumps(assessment, indent=2) + '\n')
print(json.dumps({'all_controls_passed': True, 'tests': [r['name'] for r in records],
                  'assessment': str(target), 'source_sha256': assessment['source_sha256']}, indent=2))
