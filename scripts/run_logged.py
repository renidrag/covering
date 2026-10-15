#!/usr/bin/env python3
"""Run a bounded command; preserve command, output, versions, hashes and timing."""
import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import time
from lean_inputs import changed_paths, sha, snapshot
from record_io import write_json

class CommandInterrupted(Exception):
    def __init__(self, signum):
        self.signum = signum


def signal_group(proc, signum):
    try:
        os.killpg(proc.pid, signum)
    except ProcessLookupError:
        pass


def stop(proc):
    """Stop the owned group, including children surviving their leader."""
    signal_group(proc, signal.SIGTERM)
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    signal_group(proc, signal.SIGKILL)
    proc.wait(timeout=3)


def main(argv=None):
    os.chdir(Path(__file__).resolve().parents[1])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--name', required=True)
    parser.add_argument('--timeout', type=float, required=True)
    parser.add_argument('--memory-mib', type=int,
                        help='sample and cap the owned command group RSS')
    parser.add_argument('--output-dir', type=Path, default=Path('results'))
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    if args.command[:1] == ['--']:
        args.command = args.command[1:]
    if not args.command:
        parser.error('a command is required')
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', args.name):
        parser.error('--name must be a filename beginning with a letter or digit')
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('--timeout must be positive and finite')
    if args.memory_mib is not None and args.memory_mib <= 0:
        parser.error('--memory-mib must be positive')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    log_path = args.output_dir / (args.name + '.log')
    record_path = args.output_dir / (args.name + '.run.json')
    record = {
        'command': args.command, 'cwd': str(Path.cwd()), 'timeout_seconds': args.timeout,
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'platform': platform.platform(), 'logical_cpus': os.cpu_count(),
        'runner_python': sys.version,
        'source_hashes': {str(p): sha(p) for p in sorted(Path('scripts').glob('*.py'))},
        'watchdog_timeout': False, 'interrupted_signal': None,
    }
    record['source_hashes']['covering'] = sha(Path('covering'))
    capture_proof = Path(args.command[0]).name == 'lake'
    if capture_proof:
        record['proof_input_sha256'] = snapshot()
    executed = args.command
    if args.memory_mib is not None:
        executed = [sys.executable, 'scripts/run_memory_guard.py',
                    '--mib', str(args.memory_mib), *args.command]
    record['memory_guard_mib'] = args.memory_mib
    record['executed_command'] = executed

    def interrupted(signum, _frame):
        raise CommandInterrupted(signum)

    previous = {sig: signal.signal(sig, interrupted)
                for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)}
    start = time.monotonic()
    proc = None
    try:
        with log_path.open('w') as log:
            try:
                proc = subprocess.Popen(executed, stdout=log, stderr=subprocess.STDOUT,
                                        start_new_session=True)
                record['returncode'] = proc.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                record['watchdog_timeout'] = True
                stop(proc)
                record['returncode'] = proc.returncode
            except CommandInterrupted as exc:
                # Ignore repeated signals while the watchdog cleans up children.
                for sig in previous:
                    signal.signal(sig, signal.SIG_IGN)
                if proc is not None:
                    stop(proc)
                record['interrupted_signal'] = exc.signum
                record['returncode'] = 128 + exc.signum
            except OSError as exc:
                log.write(f'Cannot start command: {exc}\n')
                record['returncode'] = 127
    finally:
        if proc is not None and args.memory_mib is None:
            signal_group(proc, signal.SIGKILL)
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    record['elapsed_seconds'] = time.monotonic() - start
    if capture_proof:
        try:
            changes = changed_paths(record['proof_input_sha256'], snapshot())
            record['proof_inputs_unchanged'] = not changes
            record['changed_proof_inputs'] = changes
        except (OSError, ValueError, KeyError, TypeError) as exc:
            record['proof_inputs_unchanged'] = False
            record['proof_input_error'] = str(exc)
            with log_path.open('a') as log:
                log.write(f'Cannot fingerprint proof inputs after the command: {exc}\n')
    record['log_sha256'] = sha(log_path)
    write_json(record_path, record)
    print(json.dumps({k: v for k, v in record.items()
                      if k not in {'source_hashes', 'proof_input_sha256'}}, indent=2))
    if capture_proof and not record['proof_inputs_unchanged']:
        print('Proof inputs changed during the command; its record is invalid.', file=sys.stderr)
        return 1
    code = 124 if record['watchdog_timeout'] else record['returncode']
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    raise SystemExit(main())
