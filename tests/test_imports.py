"""Lean header regressions; check_lean_imports.py also checks these with Lean."""
from pathlib import Path
import sys
import unittest

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


if __name__ == '__main__':
    unittest.main()
