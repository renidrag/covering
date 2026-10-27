"""New-component boundaries and witness correspondence; no mathematical proof claims."""
from pathlib import Path
import re
import unittest
from unittest.mock import patch

from workflow_fixtures import ROOT, audit
import workflow
from check_c4k_barker import check


class C4kFamily(unittest.TestCase):
    def test_general_divisibility_is_independent_of_determinants_and_attainment(self):
        graph = audit.SourceGraph()
        paths = graph.closure('CoveringDesigns.PairDivisibility')
        self.assertIn(audit.source('CoveringDesigns.PairEquality.Classification'), paths)
        self.assertIn(audit.source('CoveringDesigns.TruncatedPlaneLoads.Actual'), paths)
        for module in audit.C4K_IMPORTS:
            if module.startswith(('CoveringDesigns.TwistedArithmetic',
                                  'CoveringDesigns.PairConstructions', 'CoveringDesigns.C4k_K_2')):
                self.assertNotIn(audit.source(module), paths)

    def test_construction_is_independent_of_lower_bounds_and_historical_witness(self):
        paths = audit.closure('CoveringDesigns.PairConstructions')
        self.assertIn(audit.source('CoveringDesigns.TwoKMinusTwo.Expansion'), paths)
        for module in audit.C4K_IMPORTS:
            if module.startswith(('CoveringDesigns.PairDivisibility',
                                  'CoveringDesigns.TwistedArithmetic', 'CoveringDesigns.C4k_K_2')):
                self.assertNotIn(audit.source(module), paths)

    def test_existing_components_do_not_acquire_new_sources(self):
        graph = audit.SourceGraph()
        new = {audit.source(m) for m in audit.C4K_IMPORTS}
        for key, info in audit.COMPONENTS.items():
            if key not in audit.C4K_COMPONENT_KEYS:
                self.assertFalse(graph.closure(info['entry']) & new, key)

    def test_all_public_source_declarations_are_audited(self):
        roots = {'pair-divisibility': 'PairDivisibility', 'twisted-arithmetic': 'TwistedArithmetic',
                 'pair-constructions': 'PairConstructions', '4k-k-2': 'C4k_K_2'}
        for key, part in roots.items():
            folder = ROOT / 'lean/CoveringDesigns'
            names = set()
            for path in [*(folder / part).glob('*.lean'), folder / (part + '.lean')]:
                text = path.read_text()
                namespace = re.search(r'^namespace ([\w.]+)', text, re.M)
                if namespace:
                    names.update(namespace[1] + '.' + name for name in re.findall(
                        r'^(?:noncomputable )?(?:def|theorem) (\w+)', text, re.M))
            if key == 'twisted-arithmetic':
                names.add('CoveringDesigns.TwistedArithmetic.instFintypeMateRepresentatives')
            self.assertEqual(names, set(audit.COMPONENTS[key]['theorems']), key)
            text = (ROOT / audit.audit_source(key)).read_text()
            for name in names:
                self.assertIn('#check (@' + name + ' :', text)
                self.assertIn('#guard_standard_axioms ' + name, text)
                self.assertIn('#print axioms ' + name, text)
            self.assertNotRegex(text, r'[∃∀] C,', 'Attaining point types must be explicit')

    def test_focused_plan_contains_the_actual_adapter_matrix_and_witness(self):
        names = {step['name'] for step in workflow.plan_for('4k-k-2', workflow.DEFAULT_LIMITS)}
        for module in ('PairDivisibility.Adapter', 'TwistedArithmetic.OrderFour',
                       'PairConstructions.Weighted', 'C4k_K_2.Barker', 'C4k_K_2.Examples'):
            self.assertIn('build-CoveringDesigns.' + module, names)
        self.assertIn('4k-k-2-audit', names)

    def test_barker_correspondence_rejects_changed_transcription(self):
        original = Path.read_text

        def changed(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if str(path).endswith('C4k_K_2/Barker.lean'):
                return text.replace('{0, 1, 2, 3', '{1, 1, 2, 3', 1)
            return text

        with patch.object(Path, 'read_text', changed), self.assertRaisesRegex(
                AssertionError, 'ordered transcription'):
            check()


if __name__ == '__main__':
    unittest.main()
