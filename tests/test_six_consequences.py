"""Six-result registration and negative trust controls; Lean verifies the proofs."""
from pathlib import Path
import json
import re
import tempfile
import unittest
from unittest.mock import patch
from workflow_fixtures import audit, memory_tree, source_headers
from check_c34183_witness import check

KEYS = ('34-18-3', *audit.C1453_LIFT_KEYS)


class SixConsequencesIntegration(unittest.TestCase):
    def test_all_public_contracts_are_audited(self):
        for key in KEYS:
            module = 'C' + key.replace('-', '_')
            paths = [audit.source('CoveringDesigns.' + module),
                     *sorted((audit.ROOT / 'CoveringDesigns' / module).glob('*.lean'))]
            names = {'CoveringDesigns.' + name for path in paths for name in
                     re.findall(r'^theorem (\w+)', path.read_text(), re.M)}
            self.assertEqual(names, set(audit.COMPONENTS[key]['theorems']))
            text = audit.audit_source(key).read_text()
            for name in names:
                with self.subTest(theorem=name):
                    self.assertRegex(text, r'#check \(@' + re.escape(name) + r'\s*:')
                    self.assertIn('#guard_standard_axioms ' + name, text)
                    self.assertIn('#print axioms ' + name, text)

    def test_lifts_have_only_the_lower_seed_and_preceding_lifts(self):
        for index, key in enumerate(audit.C1453_LIFT_KEYS):
            paths = audit.closure(audit.COMPONENTS[key]['entry'])
            self.assertIn(audit.source('CoveringDesigns.C14_5_3.LowerBound'), paths)
            self.assertIn(audit.source('CoveringDesigns.Schoenheim.LowerBound'), paths)
            for part in ('Witness', 'Completion28', 'Examples'):
                self.assertNotIn(audit.source('CoveringDesigns.C14_5_3.' + part), paths)
            for later in audit.C1453_LIFT_KEYS[index + 1:]:
                self.assertNotIn(audit.source('CoveringDesigns.C' + later.replace('-', '_') + '.LowerBound'), paths)
            self.assertNotIn(audit.source('CoveringDesigns.C34_18_3.Witness'), paths)

    def test_rejects_reverse_and_extra_imports(self):
        root = memory_tree(source_headers(whole=True))
        with patch.object(audit, 'ROOT', root / 'lean'):
            for module, dependency, diagnostic in (
                ('C14_5_3', 'C15_6_4', 'Established component'),
                ('TwoKMinusC', 'C34_18_3', 'Established component'),
                ('C15_6_4.LowerBound', 'C14_5_3.Witness', 'declared interface'),
                ('C19_10_8.LowerBound', 'QuadrupleAssembly.Counting', 'declared interface'),
                ('C34_18_3.Witness', 'C34_18_3.LowerBound', 'declared interface'),
                ('C34_18_3.LowerBound', 'C20_11_3.LowerBound', 'declared interface')):
                path = audit.source('CoveringDesigns.' + module)
                original = path.read_text()
                path.write_text(original + 'import CoveringDesigns.' + dependency + '\n')
                try:
                    with self.assertRaisesRegex(AssertionError, diagnostic):
                        audit.check_sources()
                finally:
                    path.write_text(original)

    def test_historical_witness_rejects_changed_data_credit_and_transcription(self):
        check()
        original = json.loads(Path('data/c34183-historical-witness.json').read_text())
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'witness.json'
            for mutation, diagnostic in (
                (lambda d: d['blocks_one_based'][0].reverse(), 'ordered block bytes'),
                (lambda d: d['source_artefact'].update(construction_credit='new construction'), 'construction credit')):
                data = json.loads(json.dumps(original))
                mutation(data)
                path.write_text(json.dumps(data))
                with self.assertRaisesRegex(AssertionError, diagnostic):
                    check(data_path=path)
            lean = Path(temporary) / 'Witness.lean'
            text = audit.source('CoveringDesigns.C34_18_3.Witness').read_text()
            # Change just one literal point, keeping the source data unchanged.
            marker = 'def knownBlocks13_34_18_3'
            head, body = text.split(marker, 1)
            body = body.replace('{0,', '{1,', 1)
            self.assertNotEqual(head + marker + body, text)
            lean.write_text(head + marker + body)
            with self.assertRaisesRegex(AssertionError, 'Lean transcription'):
                check(lean_path=lean)


if __name__ == '__main__':
    unittest.main()
