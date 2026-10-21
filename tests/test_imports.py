"""Lean header regressions; check_lean_imports.py also checks these with Lean."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import audit_library as audit


def import_spellings(module):
    escaped = '.'.join('«' + part + '»' for part in module.split('.'))
    return {
        'plain': 'import ' + module,
        'line_comment': 'import ' + module + '-- dependency',
        'trailing_block': 'import ' + module + ' /- dependency -/',
        'leading_block': '/- license -/import ' + module,
        'nested_blocks': 'import/- outer /- inner -/ outer -/' + module,
        'multiline': 'import -- next line\n/- note\n/- nested -/\n-/\n' + module,
        'escaped': 'import ' + escaped,
        'adjacent_escaped': 'import' + escaped,
        'crlf': '/- license\r\n-/\r\nimport\r\n' + module + '\r\n',
        'prelude': 'prelude import ' + module,
        'module': 'module import ' + module,
        'public': 'module public import ' + module,
        'meta': 'module meta import ' + module,
        'all': 'module import all ' + module,
        'public_meta': 'module public meta import ' + module,
        'meta_all': 'module meta import all ' + module,
        'modified_comments': 'module/-x-/public/-y-/meta/-z-/import/-w-/' + escaped,
    }


def header_cases():
    module = 'CoveringDesigns.C11_5_2'
    cases = [(name, source, [module]) for name, source in import_spellings(module).items()]
    cases.extend([
        ('same_line', 'import Mathlib import ' + module, [module]),
        ('external_first', 'import Mathlib /- comment -/\nimport ' + module, [module]),
        ('root_module', 'import «CoveringDesigns»', ['CoveringDesigns']),
        ('explorations', 'import «Explorations».Probe', ['Explorations.Probe']),
        ('extended_identifier', "import CoveringDesigns.α₁.Test'!?", ["CoveringDesigns.α₁.Test'!?"]),
        ('escaped_keyword', 'import CoveringDesigns.«import»', ['CoveringDesigns.import']),
        ('comment_text', '/-\nimport ' + module + '\n/- nested -/\n-/\n-- import ' + module, []),
        ('quoted_comment_text', '/- " -/ import ' + module, [module]),
        ('line_comment_in_block', '/- -- -/ import ' + module, [module]),
        ('doc_comment', '/-!\nimport ' + module + '\n-/', []),
        ('declaration_doc', '/--\nimport ' + module + '\n-/\ndef x := 1', []),
        ('string_in_body', 'def text := "\nimport ' + module + '\n"', []),
        ('raw_string_in_body', 'def text := r#"\nimport ' + module + '\n"#', []),
        ('quotation_in_body', 'def text := `(import ' + module + ')', []),
        ('module_body', 'module public section\ndef x := 1', []),
        ('keyword_prefix', 'moduleX\nimport ' + module, []),
    ])
    return cases


class ImportHeaders(unittest.TestCase):
    def test_header_syntax(self):
        for name, source, expected in header_cases():
            with self.subTest(name=name):
                self.assertEqual(audit.project_imports(source), expected)

    def test_aliases_fail_closed(self):
        for name in ('«CoveringDesigns/C11_5_2»', '«CoveringDesigns.C11_5_2»',
                     '«./CoveringDesigns».C11_5_2', 'CoveringDesigns.«../C11_5_2»',
                     'CoveringDesigns.«C11_5_2\\Stanton»', 'CoveringDesigns.«»',
                     '«coveringdesigns».C11_5_2'):
            with self.subTest(name=name):
                with self.assertRaisesRegex(ValueError, 'Cannot audit Lean imports'):
                    audit.project_imports('import ' + name)

    def test_malformed_headers_fail_closed(self):
        for source in ('/- unfinished', 'import /- unfinished',
                       'import «CoveringDesigns', 'import',
                       'import /-- declaration doc -/ CoveringDesigns',
                       'import CoveringDesigns./- split name -/C11_5_2',
                       'public import CoveringDesigns',
                       'module public import all CoveringDesigns'):
            with self.subTest(source=source):
                with self.assertRaisesRegex(ValueError, 'Cannot audit Lean imports'):
                    audit.project_imports(source, 'fixture.lean')


class ImportGraph(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='covering-import-graph-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name) / 'lean'
        self.root.mkdir()
        override = patch.object(audit, 'ROOT', self.root)
        override.start()
        self.addCleanup(override.stop)

    def write(self, module, content=''):
        path = audit.source(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        return path

    def test_shared_dependencies_are_parsed_once_and_returned_sets_are_isolated(self):
        base, left, right = ('CoveringDesigns.Probe.' + part for part in ('Base', 'Left', 'Right'))
        self.write(base)
        self.write(left, 'import ' + base)
        self.write(right, 'import ' + base)
        graph = audit.SourceGraph()
        with patch.object(audit, 'project_imports', wraps=audit.project_imports) as parsed:
            self.assertEqual(graph.module_order([left, right]), [base, left, right])
            left_paths = graph.closure(left)
            left_paths.clear()
            self.assertEqual(graph.closure(right), {audit.source(base), audit.source(right)})
            self.assertEqual(graph.closure(left), {audit.source(base), audit.source(left)})
            self.assertEqual(parsed.call_count, 3)

    def test_fresh_operations_reject_changed_headers_missing_files_and_cycles(self):
        first, second = 'CoveringDesigns.ProbeA', 'CoveringDesigns.ProbeB'
        path = self.write(first, 'import ' + second)
        dependency = self.write(second)
        expected = {path, dependency}
        self.assertEqual(audit.closure(first), expected)
        for content, exception, message in [
                ('import', ValueError, 'expected module identifier'),
                ('import ' + first, AssertionError, 'Import cycle'),
                ('import CoveringDesigns.Missing', AssertionError, 'Missing local import')]:
            with self.subTest(content=content):
                dependency.write_text(content)
                with self.assertRaisesRegex(exception, message):
                    audit.closure(first)
                dependency.write_text('')
                self.assertEqual(audit.closure(first), expected)
        dependency.unlink()
        with self.assertRaisesRegex(AssertionError, 'Missing local import'):
            audit.module_order([first])

    def test_fresh_operations_reject_new_external_shadowing(self):
        module = 'CoveringDesigns.Probe'
        self.write(module, 'import External.Dependency')
        self.assertEqual(audit.module_order([module]), [module])
        for shadow in [self.root / 'External', self.root / '.lake/build/lib/lean/External']:
            with self.subTest(shadow=shadow):
                shadow.mkdir(parents=True)
                with self.assertRaisesRegex(ValueError, 'project-local imports'):
                    audit.module_order([module])
                shadow.rmdir()
                self.assertEqual(audit.module_order([module]), [module])

    def test_fresh_operations_reject_file_and_directory_symlinks_and_path_case_aliases(self):
        module = 'CoveringDesigns.Probe.Child'
        original = self.write(module)
        self.assertEqual(audit.closure(module), {original})
        saved = original.with_suffix('.saved')
        original.rename(saved)
        original.symlink_to(saved)
        with self.assertRaisesRegex(ValueError, 'noncanonical local path'):
            audit.closure(module)
        original.unlink()
        saved.rename(original)
        directory = original.parent
        moved = directory.with_name('Stored')
        directory.rename(moved)
        directory.symlink_to(moved, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'noncanonical local path'):
            audit.module_order([module])
        directory.unlink()
        moved.rename(directory)
        self.assertEqual(audit.closure(module), {original})
        with self.assertRaises((AssertionError, ValueError)):
            audit.module_order(['CoveringDesigns.probe.Child'])


if __name__ == '__main__':
    unittest.main()
