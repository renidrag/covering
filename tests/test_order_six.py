"""Order-six workflow integration; only Lean supplies mathematical evidence."""
from pathlib import Path
import re
import unittest
from unittest.mock import patch

from workflow_fixtures import audit
import workflow
from order_six_registration import SIX_IMPORTS, SIX_THEOREMS
from order_six_data import check


class OrderSix(unittest.TestCase):
    def test_existing_components_are_independent(self):
        graph = audit.SourceGraph()
        new = {audit.source(m) for m in SIX_IMPORTS}
        for key, info in audit.COMPONENTS.items():
            if key != '6k-k-2':
                self.assertFalse(graph.closure(info['entry']) & new, key)

    def test_every_public_contract_is_typed_and_guarded(self):
        names = set()
        for module in SIX_IMPORTS:
            names.update('CoveringDesigns.C6k_K_2.' + name for name in re.findall(
                r'^(?:noncomputable )?(?:def|theorem) (\w+)', audit.source(module).read_text(), re.M))
        self.assertEqual(names, set(SIX_THEOREMS))
        text = audit.audit_source('6k-k-2').read_text()
        for name in names:
            for prefix in ('#check (@', '#guard_standard_axioms ', '#print axioms '):
                self.assertIn(prefix + name, text)

    def test_plan_contains_gate_completion_and_consumers(self):
        names = {s['name'] for s in workflow.plan_for('6k-k-2', workflow.DEFAULT_LIMITS)}
        for part in ('Discriminant', 'PrimeKernel', 'Isotropic', 'Matrix', 'Completion', 'LowerBound', 'Numerical'):
            self.assertIn('build-CoveringDesigns.C6k_K_2.' + part, names)
        self.assertIn('6k-k-2-audit', names)

    def test_exact_inventory_and_comparison_categories(self):
        report = check()
        self.assertEqual((report['rows'], report['pair_seeds'], report['positive_step_lifts']), (14, 2, 12))
        self.assertEqual((report['refreshed_LJCR'], report['retained_cvkt'], report['missing_comparison']), (9, 2, 3))
        self.assertEqual(report['kernel_declarations'], 28)

    def test_rejects_changed_numerical_bound(self):
        original = Path.read_text
        def changed(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if str(path).endswith('C6k_K_2/Numerical.lean'):
                return text.replace(': 596679 ≤ C.card', ': 596680 ≤ C.card', 1)
            return text
        with patch.object(Path, 'read_text', changed), self.assertRaisesRegex(AssertionError, 'correspondence'):
            check()

    def test_rejects_missing_indexed_audit(self):
        original = Path.read_text
        def changed(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if str(path).endswith('audits/C6k_K_2.lean'):
                return text.replace('#check (@CoveringDesigns.C6k_K_2.indexed_lower_78_18_8 :',
                                    '#check (@CoveringDesigns.C6k_K_2.indexed_lower_78_18_8_bad :', 1)
            return text
        with patch.object(Path, 'read_text', changed), self.assertRaises(AssertionError):
            check()


if __name__ == '__main__':
    unittest.main()
