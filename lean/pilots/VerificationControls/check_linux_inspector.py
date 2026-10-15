"""Procfs fixtures and bounded subprocess controls, runnable on either host."""
from contextlib import redirect_stderr, redirect_stdout
import errno
import io
import json
import signal
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path('scripts').resolve()))
import run_memory_guard as guard


class LinuxInspectorControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='covering-procfs-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.inspector = guard.LinuxInspector(self.root, page_size=4096)

    def process(self, pid, *, group=100, pages=16, state=b'S', name=b'a ) tricky\nname'):
        directory = self.root / str(pid)
        directory.mkdir(exist_ok=True)
        # Enumerate the actual Linux stat fields from 3 through 24.
        fields = [state, b'1', str(group).encode(), b'100', b'0', b'0', b'0',
                  b'0', b'0', b'0', b'0', b'0', b'0', b'0', b'0', b'20',
                  b'0', b'1', b'0', b'12345', b'1048576', str(pages).encode()]
        path = directory / 'stat'
        path.write_bytes(str(pid).encode() + b' (' + name + b') ' + b' '.join(fields) + b'\n')
        return path

    def test_aggregate_isolation_and_zombies(self):
        self.process(101, pages=16)
        self.process(102, pages=32)
        self.process(103, state=b'Z')
        # An unrelated PID's unreadable or malformed RSS must not be accessed.
        self.process(200, group=200, pages=10**9).write_bytes(b'invalid')
        with patch.object(guard.os, 'getpgid', side_effect=lambda pid: 200 if pid == 200 else 100):
            self.assertEqual(self.inspector.sample(100), (48*4096, 32*4096, 3))
            self.assertEqual(self.inspector.members(100), {101, 102})

    def run_guard(self, exit_code, *, permanently_missing=False):
        # Simulate a leader visible in procfs before waitpid can reap it.
        proc = Mock(pid=100)
        if permanently_missing:
            proc.poll.return_value = None
        else:
            proc.poll.side_effect = [None, None, exit_code]
        output, errors = io.StringIO(), io.StringIO()
        with patch.object(guard, 'make_inspector', return_value=self.inspector), \
             patch.object(guard.os, 'getpgid', return_value=100), \
             patch.object(guard.subprocess, 'Popen', return_value=proc), \
             patch.object(guard, 'stop_group', return_value=exit_code) as cleanup, \
             patch.object(guard.time, 'sleep'), \
             patch.object(guard.time, 'monotonic', side_effect=[0.0, 1.0]), \
             redirect_stdout(output), redirect_stderr(errors):
            result = guard.main(['--mib', '128', 'unused-workload'])
        summary = json.loads(next(line.removeprefix('memory_guard_result ')
                                  for line in output.getvalue().splitlines()
                                  if line.startswith('memory_guard_result ')))
        cleanup.assert_called_once()
        return result, summary, errors.getvalue()

    def test_zombie_pending_reap_preserves_exit_status(self):
        for exit_code, expected in ((0, 0), (7, 7), (-signal.SIGTERM, 143)):
            with self.subTest(exit_code=exit_code):
                self.process(100, state=b'Z', pages=0)
                result, summary, errors = self.run_guard(exit_code)
                self.assertEqual(result, expected, errors)
                self.assertEqual(summary['outcome'], 'exit')
                self.assertEqual(summary['child_returncode'], exit_code)
                self.assertEqual(summary['observed_peak_group_rss_bytes'], 0)
                self.assertEqual(errors, '')

    def test_exited_members_are_visible_to_sampling_only(self):
        for state in (b'Z', b'X', b'x'):
            with self.subTest(state=state):
                self.process(100, state=state, pages=10**9)
                with patch.object(guard.os, 'getpgid', return_value=100):
                    self.assertEqual(self.inspector.sample(100), (0, 0, 1))
                    self.assertEqual(self.inspector.members(100), set())

    def test_missing_live_command_still_fails_inspection(self):
        result, summary, errors = self.run_guard(0, permanently_missing=True)
        self.assertEqual(result, 125)
        self.assertEqual(summary['outcome'], 'watchdog_error')
        self.assertIn('missing from its owned group', errors)

    def test_exited_before_group_lookup(self):
        self.process(101)
        with patch.object(guard.os, 'getpgid', side_effect=ProcessLookupError()):
            self.assertEqual(self.inspector.sample(100), (0, 0, 0))

    def test_exit_between_group_lookup_and_stat(self):
        self.process(101).unlink()
        with patch.object(guard.os, 'getpgid', side_effect=[100, ProcessLookupError()]):
            self.assertEqual(self.inspector.sample(100), (0, 0, 0))

    def test_still_owned_missing_stat_is_failure(self):
        self.process(101).unlink()
        with patch.object(guard.os, 'getpgid', return_value=100):
            with self.assertRaises(guard.InspectionError):
                self.inspector.sample(100)

    def test_group_change_is_not_counted(self):
        self.process(101, group=200)
        with patch.object(guard.os, 'getpgid', return_value=100):
            self.assertEqual(self.inspector.sample(100), (0, 0, 0))

    def test_malformed_owned_stat_is_failure(self):
        for contents in (b'101 (bad) S 1 100', b'102 (wrong pid) ' + b'0 '*24):
            with self.subTest(contents=contents):
                self.process(101).write_bytes(contents)
                with patch.object(guard.os, 'getpgid', return_value=100):
                    with self.assertRaises(guard.InspectionError):
                        self.inspector.sample(100)
        self.process(101, pages=-1)
        with patch.object(guard.os, 'getpgid', return_value=100):
            with self.assertRaises(guard.InspectionError):
                self.inspector.sample(100)

    def test_owned_read_permission_failure_is_not_ignored(self):
        self.process(101)
        with patch.object(guard.os, 'getpgid', return_value=100), \
             patch.object(Path, 'read_bytes', side_effect=PermissionError(errno.EACCES, 'denied')):
            with self.assertRaises(guard.InspectionError):
                self.inspector.sample(100)

    def test_missing_procfs_fails_before_workload_starts(self):
        with patch.object(guard.sys, 'platform', 'linux'), \
             patch.object(guard, 'LinuxInspector', side_effect=guard.InspectionError('missing procfs')), \
             patch.object(guard.subprocess, 'Popen') as spawn:
            self.assertEqual(guard.main(['--mib', '128', 'unused-workload']), 125)
            spawn.assert_not_called()
        with self.assertRaises(guard.InspectionError):
            guard.LinuxInspector(self.root / 'missing', page_size=4096)


class CommandExitControls(unittest.TestCase):
    def run_with_samples(self, samples, *, delay, exit_code=0):
        # Keep real process creation, exit notification and cleanup; control only
        # the sampling result that exposed the shutdown race in CI.
        inspector = guard.make_inspector()
        output, errors = io.StringIO(), io.StringIO()
        finish = (f'os.kill(os.getpid(), {-exit_code})' if exit_code < 0
                  else f'sys.exit({exit_code})')
        workload = f'import os, time, sys; time.sleep({delay!r}); {finish}'
        with patch.object(guard, 'make_inspector', return_value=inspector), \
             patch.object(inspector, 'sample', side_effect=samples), \
             redirect_stdout(output), redirect_stderr(errors):
            result = guard.main(['--mib', '128', sys.executable, '-c', workload])
        summary = json.loads(next(line.removeprefix('memory_guard_result ')
                                  for line in output.getvalue().splitlines()
                                  if line.startswith('memory_guard_result ')))
        self.assertEqual(inspector.members(summary['owned_group']), set())
        return result, summary, errors.getvalue()

    def test_empty_sample_before_real_exit_preserves_status(self):
        for exit_code, expected in ((0, 0), (7, 7), (-signal.SIGTERM, 143)):
            with self.subTest(exit_code=exit_code):
                result, summary, errors = self.run_with_samples(
                    lambda _group: (0, 0, 0), delay=0.05, exit_code=exit_code)
                self.assertEqual(result, expected, errors)
                self.assertEqual(summary['outcome'], 'exit')
                self.assertEqual(summary['child_returncode'], exit_code)
                self.assertGreater(summary['empty_samples'], 0)
                self.assertEqual(errors, '')

    def test_persistent_empty_samples_stop_a_real_command(self):
        result, summary, errors = self.run_with_samples(
            lambda _group: (0, 0, 0), delay=5)
        self.assertEqual(result, 125)
        self.assertEqual(summary['outcome'], 'watchdog_error')
        self.assertIn('missing from its owned group', errors)
        self.assertNotEqual(summary['child_returncode'], 0)
        self.assertGreater(summary['empty_samples'], 1)

    def test_memory_threshold_after_empty_sample_still_stops_command(self):
        result, summary, _errors = self.run_with_samples(
            [(0, 0, 0), (129 * 1024**2, 129 * 1024**2, 1)], delay=5)
        self.assertEqual(result, 137)
        self.assertEqual(summary['outcome'], 'memory_threshold')
        self.assertNotEqual(summary['child_returncode'], 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
