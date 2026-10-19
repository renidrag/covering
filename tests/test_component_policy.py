"""Direct component policy and plan checks, with no compiler or CLI subprocess.

Every test owns its source tree. The real dependency walker and policy validator
operate on an in-memory regular-file adapter; disk/path/process controls stay in
test_cli. Named regressions complement registry-derived exhaustive checks.
"""
import unittest
from unittest.mock import patch

from workflow_fixtures import audit, memory_tree, source_headers
from test_imports import import_spellings
import workflow


class ComponentFixture:
    def setUp(self):
        self.root = memory_tree(source_headers())
        override = patch.object(audit, 'ROOT', self.root / 'lean')
        override.start()
        self.addCleanup(override.stop)

    def write(self, name, text):
        path = self.root / name
        path.write_text(text)
        return path

    def plan(self, key):
        return {'steps': workflow.plan_for(key, workflow.DEFAULT_LIMITS)}

    def reject_sources(self):
        with self.assertRaises((AssertionError, ValueError)) as caught:
            audit.check_sources()
        return str(caught.exception)


class ComponentPolicy(ComponentFixture, unittest.TestCase):

    def test_fixed_offset_paths_and_plan(self):
        rank = audit.closure('CoveringDesigns.Weighted.PartitionedRank')
        self.assertNotIn(audit.source('CoveringDesigns.Foundations.Basic'), rank)
        uniform = audit.closure('CoveringDesigns.TwoKMinusCGeneral.UniformLower')
        self.assertNotIn(audit.source('CoveringDesigns.TwoKMinusC.LargeDefect'), uniform)
        sharper = audit.closure('CoveringDesigns.TwoKMinusCGeneral.OffsetThreeLower')
        self.assertIn(audit.source('CoveringDesigns.TwoKMinusC.LargeDefect'), sharper)
        self.assertNotIn(audit.source('CoveringDesigns.Weighted.PartitionedRank'), sharper)
        upper = audit.closure('CoveringDesigns.TwoKMinusCGeneral.Attainment')
        self.assertNotIn(audit.source('CoveringDesigns.TwoKMinusCGeneral.Saturation'), upper)
        self.assertEqual(self.plan('two-k-minus-c-general')['steps'][-1]['name'],
                         'two-k-minus-c-general-audit')

    def test_partitioned_rank_rejects_covering_dependency(self):
        path = self.root / 'lean/CoveringDesigns/Weighted/PartitionedRank.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.Foundations.Basic\n')
        self.assertIn('Fixed-offset Weighted.PartitionedRank', self.reject_sources())

    def test_uniform_offset_rejects_large_defect_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusCGeneral/UniformLower.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.TwoKMinusC.LargeDefect\n')
        self.assertIn('Fixed-offset TwoKMinusCGeneral.UniformLower', self.reject_sources())

    def test_preserved_adapter_cannot_import_new_geometry(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusC/LargeDefect.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.TwoKMinusCGeneral.Geometry\n')
        self.assertIn('imports fixed-offset generalisation', self.reject_sources())

    def test_fixed_offset_rejects_numerical_c20(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusCGeneral/Geometry.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.C20_11_3.LowerBound\n')
        self.assertIn('numerical C20', self.reject_sources())

    def test_offset_adapter_boundaries_and_plan(self):
        generic = audit.closure('CoveringDesigns.TwoKMinusC.LargeDefect')
        self.assertNotIn(audit.source('CoveringDesigns.TwoKMinusC.OffsetTwo'), generic)
        self.assertNotIn(audit.source('CoveringDesigns.TwoKMinusTwo.Bounds'), generic)
        self.assertIn(audit.source('CoveringDesigns.MulticoverLargeDefect.LowerBound'), generic)
        self.assertIn(audit.source('CoveringDesigns.Multicover.Family'), generic)
        self.assertEqual(self.plan('two-k-minus-c')['steps'][-1]['name'], 'two-k-minus-c-audit')

    def test_offset_generic_rejects_saturation_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusC/LargeDefect.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.TwoKMinusTwo.Bounds\n')
        self.assertIn('TwoKMinusC LargeDefect', self.reject_sources())

    def test_offset_rejects_numerical_c20_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusC/OffsetTwo.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.C20_11_3.LowerBound\n')
        self.assertIn('numerical C20', self.reject_sources())

    def test_established_family_cannot_acquire_offset_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusTwo/Arithmetic.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.TwoKMinusC.Algebra\n')
        self.assertIn('imports TwoKMinusC', self.reject_sources())

    def test_two_k_equality_boundaries_and_plan(self):
        lower = audit.closure('CoveringDesigns.TwoKMinusTwoEquality.Bounds')
        helper = audit.closure('CoveringDesigns.BoundaryRank.Equality')
        self.assertNotIn(audit.source('CoveringDesigns.AffineConstructions.Geometry'), lower)
        self.assertNotIn(audit.source('CoveringDesigns.C20_11_3.LowerBound'), lower)
        self.assertEqual(helper, audit.closure('CoveringDesigns.BoundaryRank.Nullity') |
                         {audit.source('CoveringDesigns.BoundaryRank.Equality')})
        self.assertEqual(self.plan('two-k-minus-two-equality')['steps'][-1]['name'],
                         'two-k-minus-two-equality-audit')

    def test_two_k_equality_rejects_numerical_c20_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusTwoEquality/Bounds.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.C20_11_3.LowerBound\n')
        self.assertIn('numerical C20', self.reject_sources())


    def test_established_family_cannot_acquire_equality_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusTwo/Arithmetic.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.BoundaryRank.Equality\n')
        self.assertIn('imports equality refinement', self.reject_sources())

    def test_two_k_family_boundaries_and_plan(self):
        lower = audit.closure('CoveringDesigns.TwoKMinusTwo.Bounds')
        upper = audit.closure('CoveringDesigns.TwoKMinusTwo.Construction')
        self.assertNotIn(audit.source('CoveringDesigns.AffineConstructions.Geometry'), lower)
        self.assertNotIn(audit.source('CoveringDesigns.BoundaryRank.Nullity'), upper)
        self.assertIn(audit.source('CoveringDesigns.C20_11_3.Incidence'), lower)
        self.assertNotIn(audit.source('CoveringDesigns.C20_11_3'), lower | upper)
        self.assertEqual(self.plan('two-k-minus-two')['steps'][-1]['name'],
                         'two-k-minus-two-audit')

    def test_two_k_rejects_numerical_c20_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusTwo/Bounds.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.C20_11_3.LowerBound\n')
        self.assertIn('numerical C20', self.reject_sources())

    def test_two_k_arithmetic_rejects_covering_dependency(self):
        path = self.root / 'lean/CoveringDesigns/TwoKMinusTwo/Arithmetic.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.Foundations.Basic\n')
        self.assertIn('TwoKMinusTwo Arithmetic', self.reject_sources())


    def test_c20_standalone_boundary_and_plan(self):
        signless = audit.closure('CoveringDesigns.BoundaryRank.Signless')
        self.assertEqual(signless, {audit.source('CoveringDesigns.BoundaryRank.Signless')})
        nullity = audit.closure('CoveringDesigns.BoundaryRank.Nullity')
        self.assertEqual(nullity, signless | {audit.source('CoveringDesigns.BoundaryRank.Nullity')})
        paths = audit.closure('CoveringDesigns.C20_11_3')
        for forbidden in ('C11_5_2', 'C12_6_3', 'C13_7_4', 'Horsley'):
            self.assertNotIn(audit.source('CoveringDesigns.' + forbidden), paths)
        self.assertEqual(self.plan('20-11-3')['steps'][-1]['name'], 'c20-11-3-audit')

    def test_boundary_rank_rejects_covering_dependency(self):
        path = self.root / 'lean/CoveringDesigns/BoundaryRank/Signless.lean'
        path.write_text(path.read_text() + 'import CoveringDesigns.Foundations.Basic\n')
        self.assertIn('C20_11_3 BoundaryRank.Signless', self.reject_sources())























    def test_general_bound_component_has_its_own_registered_plan(self):
        plan = self.plan('schoenheim')
        self.assertEqual([step['name'] for step in plan['steps']], ['build-CoveringDesigns.Schoenheim', 'schoenheim-audit'])
        self.assertEqual(plan['steps'][-1]['command'][-1], 'lean/audits/Schoenheim.lean')







    def test_point_reduction_plan(self):
        info = audit.COMPONENTS['point-reduction']
        plan = self.plan('point-reduction')
        names = [step['name'] for step in plan['steps']]
        self.assertEqual(names[-1], 'point-reduction-audit')
        prefix = 'build-CoveringDesigns.PointReduction.'
        for earlier, later in [('Basic', 'Bounds'), ('Bounds', 'Family'), ('Family', 'Examples')]:
            self.assertLess(names.index(prefix + earlier), names.index(prefix + later))
        for forbidden in ('AffineConstructions', 'BaseAffine', 'Horsley.Matrix', 'MulticoverIncidence.Matrices', 'CaroTuza', 'Multicover.Examples'):
            self.assertNotIn('build-CoveringDesigns.' + forbidden, names)












    def test_multicover_large_defect_plan(self):
        info = audit.COMPONENTS['multicover-large-defect']
        plan = self.plan('multicover-large-defect')
        names = [step['name'] for step in plan['steps']]
        self.assertEqual(names[-1], 'multicover-large-defect-audit')
        for first, second in (('Counting', 'LowerBound'), ('Selection', 'LowerBound'), ('LowerBound', 'Family'), ('LowerBound', 'Examples')):
            self.assertLess(names.index('build-CoveringDesigns.MulticoverLargeDefect.' + first), names.index('build-CoveringDesigns.MulticoverLargeDefect.' + second))
        self.assertNotIn('build-CoveringDesigns.LargeDefect.Pairs', names)
        self.assertNotIn('build-CoveringDesigns.MulticoverIncidence.Examples', names)


    def test_multicover_plan(self):
        info = audit.COMPONENTS['multicover']
        plan = self.plan('multicover')
        names = [step['name'] for step in plan['steps']]
        self.assertEqual(names[-1], 'multicover-audit')
        for first, second in (('Basic', 'Links'), ('Links', 'Counting'), ('Counting', 'Schoenheim'), ('Schoenheim', 'Family'), ('Schoenheim', 'Multiset'), ('Family', 'Examples')):
            self.assertLess(names.index('build-CoveringDesigns.Multicover.' + first), names.index('build-CoveringDesigns.Multicover.' + second))
        self.assertNotIn('build-CoveringDesigns.HorsleySingh.LowerBound', names)
        self.assertNotIn('build-CoveringDesigns.HigherIncidence.LowerBound', names)





    def test_caro_tuza_plan(self):
        info = audit.COMPONENTS['caro-tuza']
        plan = self.plan('caro-tuza')
        names = [step['name'] for step in plan['steps']]
        self.assertEqual(names, ['build-CoveringDesigns.CaroTuza.' + name for name in ('Function', 'Graph', 'Selection', 'Examples')] + ['build-CoveringDesigns.CaroTuza', 'caro-tuza-audit'])


    def test_weighted_foundations_plan(self):
        info = audit.COMPONENTS['weighted']
        plan = self.plan('weighted')
        names = [step['name'] for step in plan['steps']]
        self.assertEqual(names[-1], 'weighted-audit')
        self.assertLess(names.index('build-CoveringDesigns.Weighted.Matrix'), names.index('build-CoveringDesigns.Weighted.Pairs'))
        self.assertLess(names.index('build-CoveringDesigns.Weighted.Counting'), names.index('build-CoveringDesigns.Weighted.Examples'))
        self.assertNotIn('build-CoveringDesigns.Applications.ZeroDefect', names)












    def test_point_reduction_dependency_boundaries(self):
        cases = [('Basic', 'CoveringDesigns.Multicover.Family'), ('Bounds', 'CoveringDesigns.AffineConstructions.Transformations'), ('Family', 'CoveringDesigns.PointReduction.Examples')]
        for module, forbidden in cases:
            with self.subTest(module=module, forbidden=forbidden):
                path = self.root / str(audit.source('CoveringDesigns.PointReduction.' + module))
                original = path.read_text()
                path.write_text(original + 'import ' + forbidden + '\n')
                self.reject_sources()
                path.write_text(original)












    def test_multicover_large_defect_dependency_boundaries(self):
        cases = [('Counting', 'CoveringDesigns.Weighted.Matrix'), ('Counting', 'CoveringDesigns.CaroTuza.Selection'), ('Selection', 'CoveringDesigns.LargeDefect.Selection'), ('LowerBound', 'CoveringDesigns.LargeDefect.LowerBound'), ('LowerBound', 'CoveringDesigns.MulticoverIncidence.Family'), ('LowerBound', 'CoveringDesigns.MulticoverLargeDefect.Family'), ('LowerBound', 'CoveringDesigns.MulticoverLargeDefect.Examples'), ('Family', 'CoveringDesigns.LargeDefect.Examples'), ('Examples', 'CoveringDesigns.MulticoverIncidence.Examples'), ('Examples', 'CoveringDesigns.CaroTuza.Examples')]
        for module, forbidden in cases:
            with self.subTest(module=module, forbidden=forbidden):
                path = self.root / str(audit.source('CoveringDesigns.MulticoverLargeDefect.' + module))
                original = path.read_text()
                path.write_text(original + 'import ' + forbidden + '\n')
                self.reject_sources()
                path.write_text(original)


    def test_multicover_dependency_boundaries(self):
        cases = [('Basic', 'CoveringDesigns.Schoenheim.LowerBound'), ('Links', 'CoveringDesigns.Multicover.Counting'), ('Schoenheim', 'CoveringDesigns.Multicover.Family'), ('Schoenheim', 'CoveringDesigns.Multicover.Multiset'), ('Schoenheim', 'CoveringDesigns.Multicover.Examples'), ('Schoenheim', 'CoveringDesigns.HorsleySingh.SubsetLinks'), ('Family', 'CoveringDesigns.HorsleySingh.LowerBound'), ('Multiset', 'CoveringDesigns.Applications.ZeroDefect'), ('Examples', 'CoveringDesigns.Schoenheim.Examples')]
        for module, forbidden in cases:
            with self.subTest(module=module, forbidden=forbidden):
                path = self.root / str(audit.source('CoveringDesigns.Multicover.' + module))
                original = path.read_text()
                path.write_text(original + 'import ' + forbidden + '\n')
                self.reject_sources()
                path.write_text(original)





    def test_caro_tuza_dependency_boundaries(self):
        cases = [('Function', 'CoveringDesigns.CaroTuza.Graph'), ('Selection', 'CoveringDesigns.CaroTuza.Examples'), ('Selection', 'CoveringDesigns.Applications.ZeroDefect'), ('Graph', 'CoveringDesigns.Combinatorics.WeightedPartition')]
        for module, forbidden in cases:
            with self.subTest(module=module, forbidden=forbidden):
                path = self.root / str(audit.source('CoveringDesigns.CaroTuza.' + module))
                original = path.read_text()
                path.write_text(original + 'import ' + forbidden + '\n')
                self.reject_sources()
                path.write_text(original)


    def test_weighted_foundations_dependency_boundaries(self):
        cases = [('CoveringDesigns.Weighted.Matrix', 'CoveringDesigns.HorsleySingh'), ('CoveringDesigns.Weighted.Counting', 'CoveringDesigns.Weighted.Matrix'), ('CoveringDesigns.Weighted.Counting', 'CoveringDesigns.HorsleySingh'), ('CoveringDesigns.Weighted.Pairs', 'CoveringDesigns.Applications.ZeroDefect')]
        for module, forbidden in cases:
            with self.subTest(module=module, forbidden=forbidden):
                path = self.root / str(audit.source(module))
                original = path.read_text()
                path.write_text(original + 'import ' + forbidden + '\n')
                self.reject_sources()
                path.write_text(original)


    def test_c17_rejects_unrelated_results(self):
        for key in ('11-5-2', '12-6-3', '13-7-4'):
            with self.subTest(component=key):
                self.write('lean/CoveringDesigns/C17_9_5.lean', 'import CoveringDesigns.Applications.ZeroDefect\nimport ' + audit.COMPONENTS[key]['entry'] + '\n')
                result = self.reject_sources()
                self.assertIn('17-9-5 imports an independent component', result)





    def test_general_bound_rejects_each_result_specific_dependency(self):
        for key in ('11-5-2', '12-6-3', '13-7-4'):
            with self.subTest(component=key):
                self.write('lean/CoveringDesigns/Schoenheim.lean', 'import ' + audit.COMPONENTS[key]['entry'] + '\n')
                result = self.reject_sources()
                self.assertIn('imports an independent component', result)

    def test_commented_imports_reject_each_result_specific_dependency(self):
        for key in ('11-5-2', '12-6-3', '13-7-4'):
            for suffix in (' -- dependency\n', '--dependency', ' \t--\r\n'):
                with self.subTest(component=key, suffix=suffix):
                    self.write('lean/CoveringDesigns/Schoenheim.lean', 'import ' + audit.COMPONENTS[key]['entry'] + suffix)
                    result = self.reject_sources()
                    self.assertIn('imports an independent component', result)

    def test_header_spellings_cannot_bypass_component_independence(self):
        for key in ('11-5-2', '12-6-3', '13-7-4'):
            for name, source in import_spellings(audit.COMPONENTS[key]['entry']).items():
                with self.subTest(component=key, spelling=name):
                    self.write('lean/CoveringDesigns/Schoenheim.lean', source)
                    result = self.reject_sources()
                    self.assertIn('imports an independent component', result)

    def test_weighted_partition_remains_independent(self):
        self.write('lean/CoveringDesigns/Combinatorics/WeightedPartition.lean',
                   'import CoveringDesigns.Schoenheim\n')
        self.assertIn('Weighted partition must be independent', self.reject_sources())
