"""Integration checks for new consumers; compiler tests remain the proof evidence."""
from pathlib import Path
import re
import unittest
from unittest.mock import patch

from workflow_fixtures import ROOT, audit
import workflow
from qk_registration import QK_IMPORTS, QK_THEOREMS
from check_qk_data import check


class QkCompletion(unittest.TestCase):
    def test_established_components_are_independent_of_new_modules(self):
        graph = audit.SourceGraph()
        new = {audit.source(m) for m in QK_IMPORTS}
        for key, info in audit.COMPONENTS.items():
            if key not in ('qk-k-2', 'pair-consequences', '6k-k-2'):
                self.assertFalse(graph.closure(info['entry']) & new, key)

    def test_constructions_and_lifting_have_separate_dependencies(self):
        construction = audit.closure('CoveringDesigns.Qk_K_2.Construction')
        for module in ('Numerical', 'NumericalLower', 'Exclusions', 'Equality', 'Perona', 'DeHeerMuir'):
            self.assertNotIn(audit.source('CoveringDesigns.Qk_K_2.' + module), construction)
        lifts = audit.closure('CoveringDesigns.Qk_K_2.Lifts')
        self.assertIn(audit.source('CoveringDesigns.C4k_K_2.LowerBound'), lifts)
        for module in ('Construction', 'Exact', 'Perona', 'DeHeerMuir', 'Numerical'):
            self.assertNotIn(audit.source('CoveringDesigns.Qk_K_2.' + module), lifts)

    def test_every_public_contract_is_typed_and_axiom_audited(self):
        names = set()
        for module in QK_IMPORTS:
            text = audit.source(module).read_text()
            namespace = re.search(r'^namespace ([\w.]+)', text, re.M)
            if namespace:
                names.update(namespace[1]+'.'+name for name in re.findall(
                    r'^(?:noncomputable )?(?:def|theorem) (\w+)', text, re.M))
        self.assertEqual(names, set(QK_THEOREMS))
        text = audit.audit_source('qk-k-2').read_text()
        for name in names:
            for prefix in ('#check (@', '#guard_standard_axioms ', '#print axioms '):
                self.assertIn(prefix+name, text)

    def test_plan_uses_the_new_witnesses_arithmetic_and_all_lifts(self):
        names = {step['name'] for step in workflow.plan_for('qk-k-2', workflow.DEFAULT_LIMITS)}
        for part in ('Determinant', 'Exclusions', 'Construction', 'Equality', 'Perona', 'DeHeerMuir', 'Lifts'):
            self.assertIn('build-CoveringDesigns.Qk_K_2.'+part, names)
        self.assertIn('qk-k-2-audit', names)

    def test_preserved_data_and_all_ceilings(self):
        report = check()
        self.assertEqual(report['matched_comparisons'], 53)
        self.assertEqual(report['unavailable_comparisons'], 6)

    def test_rejects_changed_witness_transcription(self):
        original = Path.read_text
        def changed(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if str(path).endswith('Qk_K_2/Perona.lean'):
                return text.replace('{0, 1, 3', '{1, 1, 3', 1)
            return text
        with patch.object(Path, 'read_text', changed), self.assertRaisesRegex(AssertionError, 'transcription'):
            check()

    def test_rejects_changed_lift_contract(self):
        original = Path.read_text
        def changed(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if str(path).endswith('Qk_K_2/Lifts.lean'):
                return text.replace(': 1007 ≤ C.card', ': 1008 ≤ C.card', 1)
            return text
        with patch.object(Path, 'read_text', changed), self.assertRaisesRegex(AssertionError, 'Lift contract'):
            check()


if __name__ == '__main__':
    unittest.main()
