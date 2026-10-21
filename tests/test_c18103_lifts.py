"""Lifting registration and trust-boundary regressions; no mathematical claims."""
from pathlib import Path
import re
import unittest
from unittest.mock import patch
from workflow_fixtures import audit, memory_tree, source_headers

KEY = 'c18103-lifts'
BASE = 'CoveringDesigns.Applications.C18103Lifts'
ROWS = [(19, 11, 4, 21), (20, 12, 5, 35), (21, 13, 6, 57),
        (22, 14, 7, 90), (23, 15, 8, 138)]

class C18103LiftsIntegration(unittest.TestCase):
    def test_complete_contract_and_expanded_coverage(self):
        names = set()
        for path in (audit.ROOT / 'CoveringDesigns/Applications/C18103Lifts').glob('*.lean'):
            names.update(BASE + '.' + n for n in re.findall(r'^theorem (\w+)', path.read_text(), re.M))
        self.assertEqual(names, set(audit.COMPONENTS[KEY]['theorems']))
        text = audit.audit_source(KEY).read_text()
        for name in names:
            self.assertRegex(text, r'#check \(@' + re.escape(name) + r'\s*:')
            self.assertIn('#guard_standard_axioms ' + name, text)
            self.assertIn('#print axioms ' + name, text)
        for v, k, t, n in ROWS:
            contract = text.split(f'theorem lower_bound_{v}_{k}_{t}_explicit', 1)[1].split('\n\n', 1)[0]
            for fragment in (f'Fintype.card α = {v}', f'∀ B ∈ C, B.card = {k}',
                             f'∀ T : Finset α, T.card = {t} → ∃ B ∈ C, T ⊆ B', f'{n} ≤ C.card'):
                self.assertIn(fragment, contract)
            self.assertNotIn('DecidableEq', contract)

    def test_dependency_boundary_rejects_witness_and_reverse_imports(self):
        root = memory_tree(source_headers(whole=True))
        with patch.object(audit, 'ROOT', root / 'lean'):
            for target, dependency, diagnostic in (
                (BASE + '.LowerBound', 'CoveringDesigns.C18_10_3.Witness', 'declared interface'),
                (BASE + '.LowerBound', 'CoveringDesigns.MulticoverLargeDefect.Family', 'declared interface'),
                ('CoveringDesigns.C18_10_3', BASE, 'Established component'),
                ('CoveringDesigns.Schoenheim', BASE, 'Established component')):
                path = audit.source(target)
                original = path.read_text()
                path.write_text(original + '\nimport ' + dependency + '\n')
                try:
                    with self.assertRaisesRegex(AssertionError, diagnostic):
                        audit.check_sources()
                finally:
                    path.write_text(original)

    def test_seed_lower_and_iterated_interface_are_reused_without_witness(self):
        paths = audit.closure(BASE)
        self.assertIn(audit.source('CoveringDesigns.C18_10_3.LowerBound'), paths)
        self.assertIn(audit.source('CoveringDesigns.Multicover.Schoenheim'), paths)
        for part in ('LiftingComparison.Applications', 'LiftingComparison.Covering',
                     'LiftingComparison.Iteration', 'MulticoverLargeDefect.Family',
                     'BoundaryRank.SquareDuality', 'C18_10_3.SquareSupport'):
            self.assertNotIn(audit.source('CoveringDesigns.' + part), paths)
        self.assertNotIn(audit.source('CoveringDesigns.C18_10_3.Witness'), paths)
        for part in ('', '.Rank', '.Saturated', '.LowerBound', '.Witness'):
            self.assertNotIn(audit.source('CoveringDesigns.C20_11_3' + part), paths)

if __name__ == '__main__':
    unittest.main()
