"""Dependency and registration boundaries of the historical equality bridge."""
import unittest
from workflow_fixtures import audit
import workflow


class PairEquality(unittest.TestCase):
    def test_geometric_core_uses_only_existing_incidence_contract(self):
        graph = audit.SourceGraph()
        root = 'CoveringDesigns.PairEquality'
        allowed = {audit.source('CoveringDesigns.' + n) for n in (
            'Foundations.Basic', 'Foundations.Intersecting',
            'TruncatedPlaneLoads.Incidence')}
        for path in graph.closure(root + '.Classification'):
            self.assertTrue(path in allowed or 'PairEquality' in path.parts, path)
        compatibility = graph.closure(root + '.Compatibility')
        for part in ('Converse', 'Integer', 'Covering', 'Actual', 'Examples'):
            self.assertNotIn(audit.source('CoveringDesigns.TruncatedPlaneLoads.' + part), compatibility)

    def test_existing_components_do_not_acquire_classification(self):
        graph = audit.SourceGraph()
        new_sources = {audit.source(m) for m in audit.PAIR_EQUALITY_IMPORTS}
        for key, info in audit.COMPONENTS.items():
            if key in audit.C4K_COMPONENT_KEYS:
                continue  # New declared consumers have separate dependency-boundary tests.
            if key != 'pair-equality':
                self.assertFalse(graph.closure(info['entry']) & new_sources, key)

    def test_focused_plan_compiles_controls_and_audits_contracts(self):
        plan = workflow.plan_for('pair-equality', workflow.DEFAULT_LIMITS)
        names = [step['name'] for step in plan]
        self.assertIn('build-CoveringDesigns.PairEquality.Extraction', names)
        self.assertIn('build-CoveringDesigns.PairEquality.Examples', names)
        self.assertEqual(names[-1], 'pair-equality-audit')
        info = audit.COMPONENTS['pair-equality']
        self.assertIn('CoveringDesigns.PairEquality.IsTwistedPlane.maximal', info['theorems'])
        self.assertIn('CoveringDesigns.AuditPairEquality.twisted_explicit', info['milestones'])


if __name__ == '__main__':
    unittest.main()
