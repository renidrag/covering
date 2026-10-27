"""Atomic-record preservation for the full-library record-writing recovery."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import record_io


class AtomicRecords(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='covering-record-tests-')
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.path = self.directory / 'record.json'
        self.path.write_bytes(b'previous complete record\n')

    def assert_previous_preserved(self):
        self.assertEqual(self.path.read_bytes(), b'previous complete record\n')
        self.assertEqual(list(self.directory.iterdir()), [self.path])

    def test_exact_record_bytes_and_atomic_replacement(self):
        value = {'nested': [True, None, {'unicode': 'π', 'escaped': '\n'}], 'count': 43}
        expected = (b'{\n  "nested": [\n    true,\n    null,\n    {\n'
                    b'      "unicode": "\\u03c0",\n      "escaped": "\\n"\n'
                    b'    }\n  ],\n  "count": 43\n}\n')
        replace = Path.replace
        def inspect_replace(temporary, destination):
            self.assertEqual(destination, self.path)
            self.assertEqual(self.path.read_bytes(), b'previous complete record\n')
            self.assertEqual(temporary.read_bytes(), expected)
            return replace(temporary, destination)
        with patch.object(Path, 'replace', inspect_replace):
            record_io.write_json(self.path, value)
        self.assertEqual(self.path.read_bytes(), expected)
        self.assertEqual(json.loads(self.path.read_text()), value)
        self.assertEqual(list(self.directory.iterdir()), [self.path])

    def test_serialization_failure_keeps_previous_record(self):
        with self.assertRaises(TypeError):
            record_io.write_json(self.path, {'not_serializable': object()})
        self.assert_previous_preserved()

    def test_sync_failure_keeps_previous_record(self):
        with patch.object(record_io.os, 'fsync', side_effect=OSError('sync failed')):
            with self.assertRaisesRegex(OSError, 'sync failed'):
                record_io.write_json(self.path, {'complete': True})
        self.assert_previous_preserved()

    def test_replace_failure_keeps_previous_record(self):
        with patch.object(Path, 'replace', side_effect=OSError('replace failed')):
            with self.assertRaisesRegex(OSError, 'replace failed'):
                record_io.write_json(self.path, {'complete': True})
        self.assert_previous_preserved()


if __name__ == '__main__':
    unittest.main()
