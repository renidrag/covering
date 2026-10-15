#!/usr/bin/env python3
"""Run a command with a sampled process-group RSS watchdog on macOS or Linux.

The command starts a new session/process group. Only that owned group is
measured and signalled: macOS uses libproc, Linux uses /proc and getpgid.
Sampling runs every 20 ms plus inspection time. Kernel RSS figures may lag.
The RSS sum can double-count shared pages. This is not an OS allocation limit:
short peaks can be missed, growth can overshoot between samples, and processes
that deliberately leave the group are outside this watchdog. Other local jobs
and the watchdog process itself are not included. Lean's -M limit is separate.

Exit 137 means the observed aggregate exceeded --mib; 125 means inspection or
watchdog failure. Otherwise preserve the command's exit status (128+signal for
a signal). SIGTERM/SIGINT/SIGHUP are forwarded and followed by group cleanup,
so this wrapper can itself be bounded by scripts/run_logged.py.
"""
import argparse
import ctypes
import errno
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

INTERVAL = 0.020
EMPTY_SAMPLE_GRACE = 0.200


class InspectionError(RuntimeError):
    pass


class RUsageInfoV0(ctypes.Structure):
    # macOS <sys/resource.h>, RUSAGE_INFO_V0. libproc supports live and zombie PIDs.
    _fields_ = [('uuid', ctypes.c_uint8 * 16)] + [
        (name, ctypes.c_uint64) for name in (
            'user_time', 'system_time', 'pkg_idle_wkups', 'interrupt_wkups',
            'pageins', 'wired_size', 'resident_size', 'phys_footprint',
            'proc_start_abstime', 'proc_exit_abstime')]


class MacOSInspector:
    backend = 'macos-libproc'

    def __init__(self):
        self.lib = ctypes.CDLL('/usr/lib/libproc.dylib', use_errno=True)
        self.listpids = self.lib.proc_listpids
        self.listpids.argtypes = [ctypes.c_uint32, ctypes.c_uint32,
                                 ctypes.c_void_p, ctypes.c_int]
        self.listpids.restype = ctypes.c_int
        self.rusage = self.lib.proc_pid_rusage
        self.rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
        self.rusage.restype = ctypes.c_int

    def members(self, group):
        capacity = 64
        while capacity <= 65536:
            buffer = (ctypes.c_int * capacity)()
            ctypes.set_errno(0)
            size = self.listpids(2, group, buffer, ctypes.sizeof(buffer))
            error = ctypes.get_errno()
            if size < 0 or (size == 0 and error):
                raise InspectionError(f'Cannot list owned group {group}: errno {error}')
            if size % ctypes.sizeof(ctypes.c_int):
                raise InspectionError(f'Invalid PID-list byte count: {size}')
            if size < ctypes.sizeof(buffer):
                return {int(pid) for pid in buffer[:size // ctypes.sizeof(ctypes.c_int)]
                        if pid > 0}
            # A full buffer may have truncated the group; never accept that sample.
            capacity = max(capacity * 2, size // ctypes.sizeof(ctypes.c_int) + 1)
        raise InspectionError('Owned group is too large to inspect completely')

    def sample(self, group):
        members = self.members(group)
        total = largest = 0
        for pid in members:
            info = RUsageInfoV0()
            ctypes.set_errno(0)
            result = self.rusage(pid, 0, ctypes.byref(info))
            error = ctypes.get_errno()
            if result != 0:
                # A process can exit between listing and querying. Ignore it only
                # after an ESRCH and a fresh group listing confirm it has gone.
                if error == errno.ESRCH and pid not in self.members(group):
                    continue
                raise InspectionError(f'Cannot read RSS for owned PID {pid}: errno {error}')
            rss = int(info.resident_size)
            total += rss
            largest = max(largest, rss)
        return total, largest, len(members)


class LinuxInspector:
    """Read owned group members from procfs, without reading unrelated RSS."""
    backend = 'linux-proc'

    def __init__(self, proc_root='/proc', page_size=None):
        self.root = Path(proc_root)
        self.page_size = os.sysconf('SC_PAGE_SIZE') if page_size is None else page_size
        if not self.root.is_dir() or self.page_size <= 0:
            raise InspectionError('Linux monitoring requires readable procfs and a page size')

    @staticmethod
    def group_of(pid):
        try:
            return os.getpgid(pid)
        except ProcessLookupError:
            return None
        except OSError as exc:
            raise InspectionError(f'Cannot identify group of PID {pid}: {exc}') from exc

    @staticmethod
    def parse_stat(data, pid):
        # Fields 3, 5 and 24 are state, process group and RSS (in pages).
        # comm may contain spaces, newlines and closing parentheses.
        # https://www.kernel.org/doc/html/latest/filesystems/proc.html
        head, separator, tail = data.rpartition(b')')
        fields = tail.split()
        try:
            if (not separator or not head.startswith(str(pid).encode() + b' (')
                    or len(fields) < 22 or len(fields[0]) != 1):
                raise ValueError('missing stat fields')
            group, pages = int(fields[2]), int(fields[21])
            if group <= 0 or pages < 0:
                raise ValueError('invalid group or RSS')
        except ValueError as exc:
            raise InspectionError(f'Invalid procfs stat for owned PID {pid}') from exc
        return fields[0], group, pages

    def processes(self, group, *, include_exited=False):
        try:
            entries = list(self.root.iterdir())
        except OSError as exc:
            raise InspectionError(f'Cannot enumerate procfs: {exc}') from exc
        for entry in entries:
            if not entry.name.isdecimal():
                continue
            pid = int(entry.name)
            if self.group_of(pid) != group:
                continue
            try:
                data = (entry / 'stat').read_bytes()
            except OSError as exc:
                # An owned process may exit, be reaped, or leave the group
                # between getpgid and read. A still-owned unreadable PID fails.
                if exc.errno in (errno.ENOENT, errno.ESRCH) and self.group_of(pid) != group:
                    continue
                raise InspectionError(f'Cannot read RSS for owned PID {pid}: {exc}') from exc
            state, observed_group, pages = self.parse_stat(data, pid)
            if observed_group != group:
                continue
            exited = state in (b'Z', b'X', b'x')
            # A zombie leader may remain visible before waitpid can reap it.
            # Count it (with zero RSS) in samples, so normal shutdown is not
            # mistaken for a missing live command. Cleanup excludes it: its
            # reaping belongs to its parent, possibly PID 1.
            if not exited or include_exited:
                yield pid, 0 if exited else pages * self.page_size

    def members(self, group):
        return {pid for pid, _rss in self.processes(group)}

    def sample(self, group):
        rss = [rss for _pid, rss in self.processes(group, include_exited=True)]
        return sum(rss), max(rss, default=0), len(rss)


def make_inspector():
    if sys.platform == 'darwin':
        return MacOSInspector()
    if sys.platform.startswith('linux'):
        return LinuxInspector()
    raise InspectionError('The sampled memory watchdog supports macOS and Linux; '
                          'use the ordinary Lean build/audit on other platforms')


def signal_group(group, signum, inspector=None):
    try:
        os.killpg(group, signum)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        # In the sandbox, a second signal to an already vanished child group
        # can report EPERM instead of ESRCH. Ignore it only when the inspector
        # confirms no live owned members; an uninspectable group remains fatal.
        if not (inspector or make_inspector()).members(group):
            return False
        raise


def stop_group(proc, immediate, inspector):
    # Also remove any group members left behind by a normally exiting leader.
    proc.poll()
    if not immediate and signal_group(proc.pid, signal.SIGTERM, inspector):
        time.sleep(0.2)
    proc.poll()
    signal_group(proc.pid, signal.SIGKILL, inspector)
    try:
        return proc.wait(timeout=2)
    except subprocess.TimeoutExpired as exc:
        raise InspectionError('Owned command did not exit after SIGKILL') from exc


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mib', type=int, required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    if args.command[:1] == ['--']:
        args.command = args.command[1:]
    if args.mib <= 0 or not args.command:
        parser.error('a positive --mib and a command are required')
    try:
        inspector = make_inspector()
    except Exception as exc:
        print(f'memory_guard: inspection unavailable; command not started: {exc}',
              file=sys.stderr, flush=True)
        return 125

    proc = None
    received = []

    def forward(signum, _frame):
        received.append(signum)
        if proc is not None:
            signal_group(proc.pid, signum, inspector)

    previous = {sig: signal.signal(sig, forward)
                for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP)}
    peak = largest = peak_members = samples = 0
    empty_samples = 0
    missing_since = None
    outcome = 'exit'
    code = 125
    child_code = None
    try:
        proc = subprocess.Popen(args.command, start_new_session=True)
        print('memory_guard_start ' + json.dumps({
            'owned_group': proc.pid, 'limit_mib': args.mib,
            'inspection_backend': inspector.backend,
            'sample_interval_seconds': INTERVAL,
            'empty_sample_grace_seconds': EMPTY_SAMPLE_GRACE,
            'scope': 'sampled aggregate RSS of the owned command process group'}), flush=True)
        while True:
            if received:
                outcome, code = 'signal', 128 + received[0]
                break
            child_code = proc.poll()
            if child_code is not None:
                code = child_code if child_code >= 0 else 128 - child_code
                break
            rss, process_max, count = inspector.sample(proc.pid)
            if count == 0:
                empty_samples += 1
            if count == 0 and proc.poll() is None:
                # A process scan and an exit notification are not atomic.
                # Keep sampling during a bounded grace period; only poll()
                # can establish the command's actual exit status.
                now = time.monotonic()
                if missing_since is None:
                    missing_since = now
                elif now - missing_since >= EMPTY_SAMPLE_GRACE:
                    raise InspectionError('The live command is missing from its owned group '
                                          f'for {EMPTY_SAMPLE_GRACE:g}s')
            else:
                missing_since = None
            samples += 1
            peak, largest, peak_members = max(peak, rss), max(largest, process_max), max(peak_members, count)
            if rss > args.mib * 1024**2:
                outcome, code = 'memory_threshold', 137
                break
            time.sleep(INTERVAL)
    except BaseException as exc:
        outcome, code = 'watchdog_error', 125
        print(f'memory_guard: {exc}', file=sys.stderr, flush=True)
    finally:
        if proc is not None:
            try:
                child_code = stop_group(proc, immediate=outcome in ('memory_threshold', 'watchdog_error'),
                                        inspector=inspector)
            except Exception as exc:
                outcome, code = 'cleanup_error', 125
                print(f'memory_guard: cleanup failed: {exc}', file=sys.stderr, flush=True)
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        print('memory_guard_result ' + json.dumps({
            'owned_group': proc.pid if proc is not None else None,
            'inspection_backend': inspector.backend,
            'outcome': outcome, 'returncode': code, 'child_returncode': child_code,
            'limit_mib': args.mib, 'samples': samples,
            'empty_samples': empty_samples,
            'observed_peak_group_rss_bytes': peak,
            'observed_largest_process_rss_bytes': largest,
            'peak_group_members': peak_members}), flush=True)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
