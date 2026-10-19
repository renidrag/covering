"""Fast audit-policy regressions using the production component validator.

The original component-specific cases are retained below. General tests also
exercise every registered theorem. Process/record rejection remains covered by
test_cli.py; these tests make no Lean proof or process-isolation claims.
"""
from itertools import combinations
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
import audit_library as audit


def required_names(key):
    info = audit.COMPONENTS[key]
    return list(dict.fromkeys(info['theorems'] + info['milestones'] + [audit.explicit_theorem(key)]))


def audit_log(key, *, omit=None, theorem=None, axioms=None):
    ordinary = ', '.join(sorted(audit.ORDINARY))
    return '\n'.join(
        "'" + name + "' depends on axioms: [" +
        (axioms if name == theorem else ordinary) + "]"
        for name in required_names(key) if name != omit)


class AuditPolicy(unittest.TestCase):
    def test_foundational_axiom_policy_is_exact(self):
        self.assertEqual(audit.ORDINARY, {'propext', 'Classical.choice', 'Quot.sound'})

    def test_malformed_output_and_contradictory_exact_contracts(self):
        for key in audit.COMPONENTS:
            principal = audit.principal_theorem(key)
            explicit = audit.explicit_theorem(key)
            valid = audit_log(key)
            line = next(line for line in valid.splitlines() if line.startswith("'" + principal + "'"))
            for malformed in (line[:-1], line.replace('depends on axioms:', 'axioms:'),
                              line.replace(principal, principal + '_different')):
                with self.subTest(component=key, malformed=malformed), self.assertRaises(AssertionError):
                    audit.component_axioms(key, valid.replace(line, malformed))
            # The principal and restatement cannot give contradictory exact
            # axiom claims, including the no-axioms output spelling.
            for name in (principal, explicit):
                contradictory = audit_log(key, theorem=name, axioms='').replace(
                    "'" + name + "' depends on axioms: []",
                    "'" + name + "' does not depend on any axioms")
                with self.subTest(component=key, contradictory=name), self.assertRaises(AssertionError):
                    audit.component_axioms(key, contradictory)

    def check_audit(self, key, *, expected=0, env=None):
        overrides = env or {}
        log = audit_log(key, omit=overrides.get('FAKE_OMIT_THEOREM'),
                        theorem=overrides.get('FAKE_AXIOMS_THEOREM'),
                        axioms=overrides.get('FAKE_AXIOMS'))
        if expected:
            self.assertEqual(expected, 1)
            with self.assertRaises(AssertionError):
                audit.component_axioms(key, log)
        else:
            checked = audit.component_axioms(key, log)
            self.assertEqual(set(checked), set(required_names(key)))
            for name in (audit.principal_theorem(key), audit.explicit_theorem(key)):
                self.assertEqual(set(checked[name]), audit.ORDINARY)
            return checked

    def test_every_registered_contract_is_present_and_required(self):
        for key in audit.COMPONENTS:
            names = required_names(key)
            with self.subTest(component=key, valid=True):
                self.assertIn(audit.principal_theorem(key), names)
                self.check_audit(key)
            for name in names:
                with self.subTest(component=key, omitted=name):
                    with self.assertRaisesRegex(AssertionError, re.escape(name)):
                        audit.component_axioms(key, audit_log(key, omit=name))

    def test_every_registered_contract_rejects_nonstandard_axioms(self):
        for key in audit.COMPONENTS:
            for name in required_names(key):
                for forbidden in ('sorryAx', 'Lean.ofReduceBool', 'Custom.unproved'):
                    with self.subTest(component=key, theorem=name, axiom=forbidden):
                        log = audit_log(key, theorem=name, axioms='propext, ' + forbidden)
                        with self.assertRaisesRegex(AssertionError, 'Nonstandard axioms in ' + re.escape(name)):
                            audit.component_axioms(key, log)

    def test_exact_principal_and_restatement_axioms_for_every_component(self):
        ordinary = sorted(audit.ORDINARY)
        for key in audit.COMPONENTS:
            for name in (audit.principal_theorem(key), audit.explicit_theorem(key)):
                for size in range(len(ordinary)):
                    for subset in combinations(ordinary, size):
                        with self.subTest(component=key, theorem=name, axioms=subset):
                            with self.assertRaises(AssertionError):
                                audit.component_axioms(key, audit_log(
                                    key, theorem=name, axioms=', '.join(subset)))

    def test_auxiliary_contracts_accept_every_standard_axiom_subset(self):
        ordinary = sorted(audit.ORDINARY)
        for key in audit.COMPONENTS:
            exact = {audit.principal_theorem(key), audit.explicit_theorem(key)}
            names = required_names(key)
            # All auxiliaries can have the same permitted subset in one valid
            # log. Check every (theorem, subset) outcome without revalidating all
            # the unchanged neighbours for each individual positive case.
            # Omission/forbidden-axiom cases below remain individual negatives;
            # named regressions also retain isolated auxiliary empty sets.
            for size in range(len(ordinary) + 1):
                for subset in combinations(ordinary, size):
                    with self.subTest(component=key, axioms=subset):
                        log = '\n'.join("'" + name + "' depends on axioms: [" +
                            ', '.join(ordinary if name in exact else subset) + ']'
                            for name in names)
                        checked = audit.component_axioms(key, log)
                        for name in names:
                            if name not in exact:
                                with self.subTest(theorem=name):
                                    self.assertEqual(set(checked[name]), set(subset))

    def test_no_axioms_output_spelling(self):
        for key in audit.COMPONENTS:
            exact = {audit.principal_theorem(key), audit.explicit_theorem(key)}
            name = next(n for n in required_names(key) if n not in exact)
            log = audit_log(key, theorem=name, axioms='').replace(
                "'" + name + "' depends on axioms: []",
                "'" + name + "' does not depend on any axioms")
            with self.subTest(component=key, theorem=name):
                self.assertEqual(audit.component_axioms(key, log)[name], [])










    def test_multicover_large_defect_contract_and_axiom_guards(self):
        info = audit.COMPONENTS['multicover-large-defect']
        samples = [info['principal_theorem'], info['explicit_theorem'],
                   'CoveringDesigns.MulticoverLargeDefect.lower_bound_inequality',
                   'CoveringDesigns.MulticoverLargeDefect.natExcess_degree',
                   'CoveringDesigns.MulticoverLargeDefect.selection_bound',
                   'CoveringDesigns.MulticoverLargeDefect.family_hypotheses_iff',
                   'CoveringDesigns.MulticoverLargeDefect.Examples.covering11']
        for theorem in samples:
            with self.subTest(missing=theorem):
                self.check_audit('multicover-large-defect', expected=1,
                            env=dict(FAKE_OMIT_THEOREM=theorem))
        self.check_audit('multicover-large-defect', expected=1, env=dict(FAKE_AXIOMS_THEOREM=samples[-1], FAKE_AXIOMS='propext, sorryAx'))
        self.check_audit('multicover-large-defect', env=dict(FAKE_AXIOMS_THEOREM='CoveringDesigns.MulticoverLargeDefect.Examples.seeds5_values',
            FAKE_AXIOMS=''))


    def test_multicover_contract_and_axiom_guards(self):
        info = audit.COMPONENTS['multicover']
        samples = [info['principal_theorem'], info['explicit_theorem'],
                   'CoveringDesigns.Multicover.subsetLink_multiplicity',
                   'CoveringDesigns.Multicover.multiplicity_ge_of_coverLower',
                   'CoveringDesigns.Multicover.ofFamily_isCover_one',
                   'CoveringDesigns.Multicover.multiset_lower_bound',
                   'CoveringDesigns.Multicover.Examples.lower_bound_5_3_2']
        for theorem in samples:
            with self.subTest(missing=theorem):
                self.check_audit('multicover', expected=1,
                            env=dict(FAKE_OMIT_THEOREM=theorem))
        self.check_audit('multicover', expected=1, env=dict(FAKE_AXIOMS_THEOREM=samples[-1], FAKE_AXIOMS='propext, sorryAx'))
        self.check_audit('multicover', env=dict(FAKE_AXIOMS_THEOREM='CoveringDesigns.Multicover.Examples.numerical_values', FAKE_AXIOMS=''))





    def test_caro_tuza_contract_and_axiom_guards(self):
        info = audit.COMPONENTS['caro-tuza']
        samples = [info['principal_theorem'], info['explicit_theorem'],
                   'CoveringDesigns.CaroTuza.potential_erase_le',
                   'CoveringDesigns.CaroTuza.UnitEdges.mono']
        for theorem in samples:
            with self.subTest(missing=theorem):
                self.check_audit('caro-tuza', expected=1,
                            env=dict(FAKE_OMIT_THEOREM=theorem))
        self.check_audit('caro-tuza', expected=1, env=dict(FAKE_AXIOMS_THEOREM=samples[-1], FAKE_AXIOMS='propext, sorryAx'))
        self.check_audit('caro-tuza', env=dict(FAKE_AXIOMS_THEOREM='CoveringDesigns.CaroTuza.f_low', FAKE_AXIOMS=''))


    def test_weighted_foundations_contract_and_axiom_guards(self):
        info = audit.COMPONENTS['weighted']
        required = info['theorems'] + info['milestones'] + [audit.explicit_theorem('weighted')]
        for theorem in required:
            with self.subTest(missing=theorem):
                self.check_audit('weighted', expected=1,
                            env=dict(FAKE_OMIT_THEOREM=theorem))
        for theorem in (info['theorems'][1], info['theorems'][3], info['milestones'][0]):
            with self.subTest(nonstandard=theorem):
                self.check_audit('weighted', expected=1, env=dict(FAKE_AXIOMS_THEOREM=theorem, FAKE_AXIOMS='propext, sorryAx'))
        self.check_audit('weighted', env=dict(FAKE_AXIOMS_THEOREM=info['milestones'][3], FAKE_AXIOMS=''))


    def test_c17_requires_all_contracts_and_standard_axioms(self):
        info = audit.COMPONENTS['17-9-5']
        principal = audit.principal_theorem('17-9-5')
        explicit = audit.explicit_theorem('17-9-5')
        required = info['theorems'] + info['milestones'] + [explicit]
        cases = [{'FAKE_OMIT_THEOREM': theorem} for theorem in required]
        cases += [
            {'FAKE_AXIOMS_THEOREM': principal, 'FAKE_AXIOMS': 'propext'},
            {'FAKE_AXIOMS_THEOREM': explicit, 'FAKE_AXIOMS': 'propext'},
            {'FAKE_AXIOMS_THEOREM': 'CoveringDesigns.WeightedPartition.potential_update',
             'FAKE_AXIOMS': 'propext, sorryAx'},
        ]
        for overrides in cases:
            with self.subTest(overrides=overrides):
                self.check_audit('17-9-5', expected=1, env=dict(**overrides))













    def test_point_reduction_named_contract_and_axiom_policy(self):
        prefix = 'CoveringDesigns.PointReduction.'
        for suffix in ('reduce_points', 'reduce_points_explicit', 'reduce_along',
                       'multiplicity_le', 'coverLower_mono', 'exists_cover_exact',
                       'family_reduce_points', 'Examples.four_repeated_triples'):
            with self.subTest(omitted=suffix), self.assertRaises(AssertionError):
                audit.component_axioms('point-reduction',
                    audit_log('point-reduction', omit=prefix + suffix))
        with self.assertRaises(AssertionError):
            audit.component_axioms('point-reduction', audit_log('point-reduction',
                theorem=prefix + 'multiplicity_le', axioms='propext, sorryAx'))
        checked = audit.component_axioms('point-reduction', audit_log('point-reduction',
            theorem=prefix + 'mem_pullback', axioms=''))
        self.assertEqual(checked[prefix + 'mem_pullback'], [])


