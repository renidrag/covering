"""C34 lift audit coverage and negative dependency controls; no proof claims."""
import re
import unittest
from unittest.mock import patch
from workflow_fixtures import audit, memory_tree, source_headers


class C34183LiftsIntegration(unittest.TestCase):
    def test_source_policy_accepts_the_registered_batch(self):
        audit.check_sources()

    def test_all_public_contracts_have_full_component_audits(self):
        for key in audit.C34183_LIFT_KEYS:
            module = 'C' + key.replace('-', '_')
            paths = [audit.source('CoveringDesigns.' + module),
                     audit.source('CoveringDesigns.' + module + '.LowerBound')]
            names = {'CoveringDesigns.' + name for path in paths for name in
                     re.findall(r'^theorem (\w+)', path.read_text(), re.M)}
            self.assertEqual(names, set(audit.COMPONENTS[key]['theorems']))
            text = audit.audit_source(key).read_text()
            for name in names:
                self.assertRegex(text, r'#check \(@' + re.escape(name) + r'\s*:')
                self.assertIn('#guard_standard_axioms ' + name, text)
                self.assertIn('#print axioms ' + name, text)
            self.assertIn('theorem lower_bound_explicit {α : Type u} [Fintype α]', text)

    def test_no_attainment_or_later_lift_dependencies(self):
        for index, key in enumerate(audit.C34183_LIFT_KEYS):
            paths = audit.closure(audit.COMPONENTS[key]['entry'])
            self.assertIn(audit.source('CoveringDesigns.C34_18_3.LowerBound'), paths)
            self.assertIn(audit.source('CoveringDesigns.Schoenheim.LowerBound'), paths)
            for module in ('C34_18_3', 'C34_18_3.Witness', 'C14_5_3.LowerBound',
                           'Applications.C18103Lifts', 'LiftingComparison'):
                self.assertNotIn(audit.source('CoveringDesigns.' + module), paths)
            for later in audit.C34183_LIFT_KEYS[index + 1:]:
                self.assertNotIn(audit.source('CoveringDesigns.C' + later.replace('-', '_') + '.LowerBound'), paths)

    def test_rejects_reverse_dependencies_and_extra_inputs(self):
        root = memory_tree(source_headers(whole=True))
        with patch.object(audit, 'ROOT', root / 'lean'):
            for module, dependency, diagnostic in (
                ('C34_18_3', 'C35_19_4', 'Established component'),
                ('TwoKMinusC', 'C39_23_8', 'Established component'),
                ('C35_19_4.LowerBound', 'C34_18_3.Witness', 'declared interface'),
                ('C36_20_5.LowerBound', 'C34_18_3', 'declared interface'),
                ('C39_23_8.LowerBound', 'QuadrupleAssembly.Counting', 'declared interface'),
                ('C38_22_7.LowerBound', 'C15_6_4.LowerBound', 'declared interface')):
                with self.subTest(module=module, dependency=dependency):
                    path = audit.source('CoveringDesigns.' + module)
                    original = path.read_text()
                    path.write_text(original + 'import CoveringDesigns.' + dependency + '\n')
                    try:
                        with self.assertRaisesRegex(AssertionError, diagnostic):
                            audit.check_sources()
                    finally:
                        path.write_text(original)


if __name__ == '__main__':
    unittest.main()
