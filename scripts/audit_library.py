#!/usr/bin/env python3
"""Compile the public proofs serially and audit their statements and dependencies.

Use --verify to check every project module in dependency order, with a time
limit and an optional memory guard for each Lean invocation. Without --verify, validate
existing records against the current inputs. Lean verifies the proofs; this
script records the checks and rejects stale records.
"""
import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import re

from lean_inputs import changed_paths, sha, snapshot, validate_snapshot

ROOT = Path('lean')
ORDINARY = {'propext', 'Classical.choice', 'Quot.sound'}
# Lean 4.34.1 Init/Meta/Defs.lean: isIdFirst and isIdRest. Python's
# Unicode \w / isalpha accept a different set of identifier characters.
_IMPORT_ID_FIRST = (
    r'[A-Za-z_\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u017f'
    r'\u0391-\u039f\u03a1-\u03a2\u03a4-\u03a9\u03b1-\u03ba\u03bc-\u03fb'
    r'\u1f00-\u1ffe\u2100-\u214f\U0001d49c-\U0001d59f]')
_IMPORT_ID = re.compile(
    _IMPORT_ID_FIRST + '(?:' + _IMPORT_ID_FIRST +
    r"|[0-9'!?\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c])*")
_LOCAL_IMPORT_ROOTS = {'CoveringDesigns', 'Explorations'}
RUNNER_INPUTS = [Path('scripts') / name for name in (
    'audit_library.py', 'verify_c13_structural.py', 'lean_inputs.py',
    'run_logged.py', 'run_memory_guard.py', 'workflow.py',
    'covering_cli.py', 'record_io.py')] + [Path('covering')]
COMPONENTS = {
    'caro-tuza': {
        'entry': 'CoveringDesigns.CaroTuza',
        'audit_name': 'caro-tuza-audit',
        'audit_file': 'CaroTuza.lean',
        'explicit_theorem': 'CoveringDesigns.AuditCaroTuza.weighted_selection_explicit',
        'principal_theorem': 'CoveringDesigns.CaroTuza.exists_selection',
        'summary_path': 'results/caro-tuza-verification.json',
        'theorems': ['CoveringDesigns.CaroTuza.' + name for name in (
            'exists_selection', 'exists_nat_selection', 'exists_selection_real',
            'potential_erase_le', 'exists_selection_of_degree_le', 'exists_selection_in')],
        'milestones': ['CoveringDesigns.CaroTuza.' + name for name in (
            'f_low', 'f_high', 'f_zero', 'f_join', 'f_nonneg', 'f_le_one', 'f_antitone',
            'decrement', 'decrement_of_le_max', 'GraphOn.mono', 'degree_nonneg',
            'degree_mono', 'weight_le_degree', 'UnitEdges.mono', 'degree_erase',
            'potential_nonneg', 'potential_le_card', 'erase_card_lt', 'nat_unitEdges',
            'Examples.empty_selection', 'Examples.edgeless', 'Examples.singleton',
            'Examples.threshold_one', 'Examples.join_one', 'Examples.parallel_edges',
            'Examples.fractional_hypotheses', 'Examples.fractional_selection',
            'Examples.zero_high_pairs', 'Examples.zero_high_selection',
            'Examples.restriction_hypotheses', 'Examples.calibration_84',
            'Examples.selection_84_degree35')],
        'independent_of': ['horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3',
                           '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality',
                           '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5'],
        'scope': 'Standalone Caro-Tuza multigraph selection (Horsley-Singh Theorem 12) and the existence form of Horsley Lemma 7 for symmetric nonnegative real weights; maximum-degree deletion, induced restriction and exact ceiling bounds. Positive high-high edges have weight at least one; zero weights remain allowed.',
    },
    'schoenheim': {
        'entry': 'CoveringDesigns.Schoenheim',
        'audit_name': 'schoenheim-audit',
        'audit_file': 'Schoenheim.lean',
        'explicit_theorem': 'CoveringDesigns.AuditSchoenheim.lower_bound_explicit',
        'principal_theorem': 'CoveringDesigns.Schoenheim.lower_bound',
        'summary_path': 'results/schoenheim-verification.json',
        'theorems': ['CoveringDesigns.Schoenheim.lower_bound',
                     'CoveringDesigns.Schoenheim.bound_of_links',
                     'CoveringDesigns.Schoenheim.lift_lower_bound'],
        'milestones': ['CoveringDesigns.Schoenheim.ceilDiv_le_iff',
                       'CoveringDesigns.Schoenheim.bound_zero',
                       'CoveringDesigns.Schoenheim.bound_succ',
                       'CoveringDesigns.Schoenheim.bound_succ_div',
                       'CoveringDesigns.Schoenheim.bound_one',
                       'CoveringDesigns.Schoenheim.bound_11_5_2',
                       'CoveringDesigns.Schoenheim.bound_12_6_3',
                       'CoveringDesigns.Schoenheim.bound_13_7_4',
                       'CoveringDesigns.Schoenheim.lower_bound_11_5_2',
                       'CoveringDesigns.Schoenheim.lower_bound_12_6_3',
                       'CoveringDesigns.Schoenheim.lower_bound_13_7_4'],
        'independent_of': ['11-5-2', '12-5-2', '12-6-3', '13-7-4'],
        'scope': "The lambda = 1 case of Schoenheim's lower-bound theorem for all 1 <= t <= k <= v, with reusable link lifting and exact integer ceilings."},
    '11-5-2': {
        'entry': 'CoveringDesigns.C11_5_2',
        'theorems': ['CoveringDesigns.stanton_classification',
                     'CoveringDesigns.stanton_classification_unique_on',
                     'CoveringDesigns.covering_number_11_5_2'],
        'milestones': ['CoveringDesigns.lower_bound_11_5_2',
                       'CoveringDesigns.stanton_representative_isCover',
                       'CoveringDesigns.stanton_representatives_not_isomorphic',
                       'CoveringDesigns.Audit11.classification_explicit',
                       'CoveringDesigns.StantonStructural.template_classification',
                       'CoveringDesigns.StantonStructural.exists_six_block_frame',
                       'CoveringDesigns.StantonStructural.SixBlockFrame.nonempty_templatePartition'],
        'independent_of': ['12-5-2', '12-6-3', '13-7-4'],
        'scope': 'Exact minimum 7 and exactly two isomorphism types of minimum coverings.'},
    '12-6-3': {
        'entry': 'CoveringDesigns.C12_6_3',
        'theorems': ['CoveringDesigns.gppt_classification',
                     'CoveringDesigns.covering_number_12_6_3'],
        'milestones': ['CoveringDesigns.gppt_structural_reduction',
                       'CoveringDesigns.GPPTStructural.template_classification',
                       'CoveringDesigns.GPPTStructural.lower_bound_fifteen',
                       'CoveringDesigns.GPPTProjective.no_duplicate_isomorphicTemplateCompletion',
                       'CoveringDesigns.figure6_isCover'],
        'independent_of': ['12-5-2', '13-7-4'],
        'scope': 'Exact minimum 15 and completeness of the 68-entry list, using the structural GPPT reduction and kernel-checked completion witnesses. Pairwise nonisomorphism is not asserted.'},
    '13-7-4': {
        'entry': 'CoveringDesigns.C13_7_4',
        'theorems': ['CoveringDesigns.covering_number_13_7_4'],
        'milestones': ['CoveringDesigns.lower_bound_30',
                       'CoveringDesigns.upper_bound_30',
                       'CoveringDesigns.C13Structural.minimum_pair_degree_seven',
                       'CoveringDesigns.C13Structural.bad_quadruple_excluded',
                       'CoveringDesigns.gppt_structural_reduction',
                       'CoveringDesigns.StantonStructural.template_classification'],
        'independent_of': ['12-5-2', 'GPPT catalogue and completion enumeration'],
        'scope': 'Exact minimum 30 by structural compatibility of minimum links, the five-point count, and the explicit thirty-block witness.'},
    '17-9-5': {
        'entry': 'CoveringDesigns.C17_9_5',
        'audit_name': 'c17-9-5-audit',
        'audit_file': 'C17_9_5.lean',
        'explicit_theorem': 'CoveringDesigns.Audit17_9_5.lower_bound_explicit',
        'principal_theorem': 'CoveringDesigns.C17_9_5.lower_bound',
        'summary_path': 'results/c17-9-5-verification.json',
        'theorems': ['CoveringDesigns.C17_9_5.lower_bound',
                     'CoveringDesigns.C17_9_5.counting_bound',
                     'CoveringDesigns.WeightedPartition.exists_balanced_partition',
                     'CoveringDesigns.Applications.ZeroDefect.zero_defect_rank_bound'],
        'milestones': ['CoveringDesigns.WeightedPartition.potential_update',
                       'CoveringDesigns.WeightedPartition.exists_large_part',
                       'CoveringDesigns.WeightedPartition.exists_bounded_partition',
                       'CoveringDesigns.WeightedPartition.exists_large_subset',
                       'CoveringDesigns.Applications.ZeroDefect.minimum_pair_excess_zero',
                       'CoveringDesigns.Applications.ZeroDefect.two_level_count',
                       'CoveringDesigns.Audit17_9_5.nonnegative_partition',
                       'CoveringDesigns.Audit17_9_5.empty_vertices',
                       'CoveringDesigns.Audit17_9_5.empty_subset',
                       'CoveringDesigns.Audit17_9_5.zero_weights',
                       'CoveringDesigns.Audit17_9_5.one_part',
                       'CoveringDesigns.Audit17_9_5.empty_part'],
        'independent_of': ['11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts'],
        'scope': 'Structural lower bound C(17,9,5) >= 60 via finite weighted partitions, zero-defect pair selection and the existing Horsley-Singh rank obstruction. No exact-value, construction or novelty claim.',
    },
    'weighted': {
        'entry': 'CoveringDesigns.Weighted',
        'audit_name': 'weighted-audit',
        'audit_file': 'Weighted.lean',
        'explicit_theorem': 'CoveringDesigns.AuditWeighted.selected_pairs_explicit',
        'principal_theorem': 'CoveringDesigns.Weighted.diagonal_add_posDef_of_weighted_row_sum_lt',
        'summary_path': 'results/weighted-verification.json',
        'theorems': ['CoveringDesigns.Weighted.diagonal_add_posDef_of_weighted_row_sum_lt',
                     'CoveringDesigns.Weighted.gram_card_le_of_weighted_row_sum_lt',
                     'CoveringDesigns.Weighted.card_le_two_levels_add_highExcess',
                     'CoveringDesigns.Weighted.two_level_bound',
                     'CoveringDesigns.Weighted.two_level_denominator_pos',
                     'CoveringDesigns.Weighted.two_level_ratio',
                     'CoveringDesigns.Weighted.two_level_ceiling',
                     'CoveringDesigns.Weighted.two_level_q',
                     'CoveringDesigns.Weighted.selected_pairs_card_le'],
        'milestones': ['CoveringDesigns.Weighted.Examples.' + name for name in (
            'unit_weights', 'weighted_two_by_two', 'zero_excess', 'empty_matrix',
            'empty_selected_pairs', 'beta_zero', 'alpha_eq_two_beta', 'empty_counting')],
        'independent_of': ['11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts',
                           '17-9-5', '47-14-5', '42-15-5'],
        'scope': 'General weighted positive definiteness, Gram-rank and real-coefficient two-level counting corresponding to Horsley-Singh Lemmas 16 and 13; selected-pair integration only, not the full arbitrary-s covering theorem.',
    },
    'multicover': {
        'entry': 'CoveringDesigns.Multicover',
        'audit_name': 'multicover-audit',
        'audit_file': 'Multicover.lean',
        'explicit_theorem': 'CoveringDesigns.AuditMulticover.lower_bound_explicit',
        'principal_theorem': 'CoveringDesigns.Multicover.lower_bound',
        'summary_path': 'results/multicover-verification.json',
        'theorems': ['CoveringDesigns.Multicover.' + name for name in (
            'lower_bound', 'multiset_lower_bound', 'subsetLink_multiplicity',
            'multiplicity_ge_of_coverLower', 'lift_lower_bound',
        )],
        'milestones': ['CoveringDesigns.Multicover.' + name for name in (
            'subsetDegree_eq_card', 'subsetDegree_empty', 'subsetDegree_singleton',
            'covers_zero_iff', 'covers_multiplicity_zero', 'covers_one_iff',
            'reindex_card', 'subsetDegree_reindex', 'degree_reindex',
            'uniform_reindex', 'covers_reindex', 'isCover_reindex',
            'subsetLink_card', 'subsetLink_uniform', 'subsetLink_isCover',
            'subset_complement_card', 'degree_sum', 'degree_sum_of_uniform',
            'subsetDegree_sum_of_uniform', 'bound_of_links', 'bound_zero',
            'bound_succ', 'bound_one_eq', 'bound_multiplicity_zero',
            'schoenheim_coverLower', 'ofFamily_card', 'ofFamily_subsetDegree',
            'ofFamily_degree', 'ofFamily_uniform', 'ofFamily_covers_one',
            'ofFamily_isCover_one', 'family_lower_bound', 'deduplicate_card_le',
            'deduplicate_isCover_one', 'ofMultiset_card', 'ofMultiset_subsetDegree',
            'ofMultiset_degree', 'ofMultiset_uniform', 'ofMultiset_isCover',
            'Examples.empty_occurrences', 'Examples.repeated_empty', 'Examples.empty_points',
            'Examples.full_copies', 'Examples.full_copies_link', 'Examples.empty_subset_link',
            'Examples.strength_zero_link', 'Examples.deduplication_loses_multiplicity', 'Examples.repeated_multiset',
            'Examples.numerical_values', 'Examples.lower_bound_4_3_2', 'Examples.lower_bound_5_3_2',
        )],
        'independent_of': ['11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley',
                           'horsley-lifts', 'equality', '17-9-5', '47-14-5', '42-15-5',
                           'weighted', 'higher-incidence', 'caro-tuza', 'large-defect',
                           'small-defect', 'small-defect-b', 'small-defect-c'],
        'scope': 'Arbitrary natural multiplicity and repeated indexed blocks: subset links, universal smaller-cover bounds, incidence counting and generalized Schoenheim for t<=k<=v. Ordinary Family and multiset adapters; zero and empty cases. No arbitrary-lambda rank theorem is claimed.',
    },
    'multicover-large-defect': {
        'entry': 'CoveringDesigns.MulticoverLargeDefect',
        'audit_name': 'multicover-large-defect-audit',
        'audit_file': 'MulticoverLargeDefect.lean',
        'explicit_theorem': 'CoveringDesigns.AuditMulticoverLargeDefect.lower_bound_explicit',
        'principal_theorem': 'CoveringDesigns.MulticoverLargeDefect.lower_bound',
        'summary_path': 'results/multicover-large-defect-verification.json',
        'theorems': ['CoveringDesigns.MulticoverLargeDefect.' + name for name in (
            'lower_bound', 'lower_bound_inequality', 'lower_bound_of_multiplicities',
            'potential_bound', 'selection_bound', 'family_lower_bound',
        )],
        'milestones': ['CoveringDesigns.MulticoverLargeDefect.' + name for name in (
            'natExcess_cast', 'natExcess_sum_cast', 'natExcess_degree',
            'independent_card_le', 'incidence_bound', 'two_level_bound',
            'two_level_ceiling', 'bound_denominator_pos', 'bound_le_iff',
            'value_nonneg', 'family_hypotheses_iff', 'value_eq_ordinary',
            'bound_eq_ordinary', 'Examples.seeds5_values', 'Examples.parameters5',
            'Examples.smaller_bounds5', 'Examples.data5', 'Examples.value5',
            'Examples.bound5', 'Examples.covering5', 'Examples.seeds10_values',
            'Examples.parameters10', 'Examples.smaller_bounds10', 'Examples.data10',
            'Examples.value10', 'Examples.bound10', 'Examples.covering10',
            'Examples.seeds11_values', 'Examples.parameters11', 'Examples.smaller_bounds11',
            'Examples.data11', 'Examples.value11', 'Examples.bound11',
            'Examples.covering11', 'Examples.counting_branches', 'Examples.coefficient_boundary',
            'Examples.adjacent_fallback', 'Examples.empty_selection', 'Examples.empty_low_classes',
            'Examples.boundary_link', 'Examples.repeated_columns', 'Examples.repeated_cover',
            'Examples.repeated_excess', 'Examples.repeated_gram',
        )],
        'independent_of': ['11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts',
                           '17-9-5', '47-14-5', '42-15-5',
                           'small-defect', 'small-defect-b', 'small-defect-c'],
        'scope': 'Horsley-Singh Theorem 15 for every positive lambda and admissible s, with repeated indexed occurrences. Full excess-graph potential and selection, both counting cases, complete universal smaller-cover hypotheses, and separate lambda-one compatibility. No Theorem 18 or constructions.',
    },
    'point-reduction': {'entry': 'CoveringDesigns.PointReduction',
 'audit_name': 'point-reduction-audit',
 'audit_file': 'PointReduction.lean',
 'explicit_theorem': 'CoveringDesigns.PointReduction.reduce_points_explicit',
 'principal_theorem': 'CoveringDesigns.PointReduction.reduce_points',
 'summary_path': 'results/point-reduction-verification.json',
 'theorems': ['CoveringDesigns.PointReduction.reduce_points',
              'CoveringDesigns.PointReduction.reduce_along',
              'CoveringDesigns.PointReduction.multiplicity_le',
              'CoveringDesigns.PointReduction.coverLower_mono',
              'CoveringDesigns.PointReduction.exists_cover_le',
              'CoveringDesigns.PointReduction.exists_cover_exact',
              'CoveringDesigns.PointReduction.family_reduce_points',
              'CoveringDesigns.PointReduction.family_lower_mono'],
 'milestones': ['CoveringDesigns.PointReduction.mem_pullback',
                'CoveringDesigns.PointReduction.pullback_card_le',
                'CoveringDesigns.PointReduction.exists_padding',
                'CoveringDesigns.PointReduction.isCover_of_padding',
                'CoveringDesigns.PointReduction.uniform_full',
                'CoveringDesigns.PointReduction.Examples.identity_reduction',
                'CoveringDesigns.PointReduction.Examples.strength_zero',
                'CoveringDesigns.PointReduction.Examples.zero_multiplicity',
                'CoveringDesigns.PointReduction.Examples.empty_reduction',
                'CoveringDesigns.PointReduction.Examples.triples_multiplicity',
                'CoveringDesigns.PointReduction.Examples.triples_cover',
                'CoveringDesigns.PointReduction.Examples.four_repeated_triples'],
 'independent_of': ['horsley',
                    'higher-incidence',
                    'weighted',
                    'multicover-incidence',
                    'exact-design',
                    'caro-tuza',
                    'large-defect',
                    'small-defect',
                    'small-defect-b',
                    'small-defect-c',
                    'multicover-large-defect',
                    'multicover-small-defect',
                    'affine-constructions',
                    'affine-schoenheim',
                    'affine-optimality',
                    'base-affine',
                    '11-5-2',
                    '12-5-2',
                    '12-6-3',
                    '13-7-4',
                    '17-9-5',
                    '47-14-5',
                    '42-15-5'],
 'scope': 'Occurrence-preserving point reduction for every natural lambda, all finite types and '
          'embeddings. Containment, multiplicity monotonicity, universal lower-bound and witness '
          'transport; lambda=1 ordinary adapter. No geometry, rank, selection or result-specific '
          'dependency.'},
}

# Additive registration of the completed discovery consequences.
COMPONENTS.update({
})


# The generic bridge is separately auditable and imports no graph application.
_PRE_TURAN_COMPONENTS = list(COMPONENTS)
COMPONENTS.update({
})


# General de Caen foundation; all public lemmas have complete typed contracts.


# Chvatal's weighted greedy foundation, independent of result-specific components.


# Gordon–Kuperberg–Patashnik section V: ordinary construction witnesses.


# Gordon–Kuperberg–Patashnik section IV: restriction and certified local repair.


# Elementary finite averaging consequence of the induced method, not a source theorem.


# Projective hyperplanes, with independent geometry and natural-number arithmetic.


# General finite-field subspace counts and GKP projective/affine flat families.


# Degree-selected ordinary witnesses; exact supplied-point construction precedes selection.


# The self-contained C(20,11,3) exclusion and its historical upper witness.
COMPONENTS['20-11-3'] = {
    'entry': 'CoveringDesigns.C20_11_3',
    'audit_name': 'c20-11-3-audit',
    'audit_file': 'C20_11_3.lean',
    'principal_theorem': 'CoveringDesigns.covering_number_20_11_3',
    'explicit_theorem': 'CoveringDesigns.Audit20_11_3.covering_number_explicit',
    'summary_path': 'results/c20-11-3-verification.json',
    'theorems': [
        'CoveringDesigns.BoundaryRank.signless_sum_squares',
        'CoveringDesigns.BoundaryRank.signless_posSemidef',
        'CoveringDesigns.BoundaryRank.kernel_restrictions',
        'CoveringDesigns.BoundaryRank.kernel_of_restrictions',
        'CoveringDesigns.BoundaryRank.ker_add_le_of_posSemidef',
        'CoveringDesigns.BoundaryRank.two_mul_finrank_le_card_of_component_constraints',
        'CoveringDesigns.BoundaryRank.two_mul_nullity_le_zero_count',
        'CoveringDesigns.BoundaryRank.gram_card_bound',
        'CoveringDesigns.C20_11_3.pair_sum',
        'CoveringDesigns.C20_11_3.pair_sum_subtype',
        'CoveringDesigns.C20_11_3.cross_pair_degree_sum',
        'CoveringDesigns.C20_11_3.cross_pair_coverage_bound',
        'CoveringDesigns.C20_11_3.mul_le_twenty_five',
        'CoveringDesigns.C20_11_3.cross_capacity_ten',
        'CoveringDesigns.C20_11_3.lower_bound_19_10_2',
        'CoveringDesigns.C20_11_3.degree_ge_six',
        'CoveringDesigns.C20_11_3.eleven_le_card',
        'CoveringDesigns.C20_11_3.degree_excess_sum',
        'CoveringDesigns.C20_11_3.degree_six_or_seven',
        'CoveringDesigns.C20_11_3.degree_profile',
        'CoveringDesigns.C20_11_3.pair_ge_two',
        'CoveringDesigns.C20_11_3.low_card',
        'CoveringDesigns.C20_11_3.lowIncidence_gram_entry',
        'CoveringDesigns.C20_11_3.low_gram',
        'CoveringDesigns.C20_11_3.lowExcess_symm',
        'CoveringDesigns.C20_11_3.lowExcess_nonneg',
        'CoveringDesigns.C20_11_3.lowExcess_diagonal',
        'CoveringDesigns.C20_11_3.highDeficit_nonneg',
        'CoveringDesigns.C20_11_3.low_row_identity',
        'CoveringDesigns.C20_11_3.high_deficit_sum',
        'CoveringDesigns.C20_11_3.zero_card_le_fourteen',
        'CoveringDesigns.C20_11_3.highDeficit_zero_card_le',
        'CoveringDesigns.C20_11_3.three_ones_posSemidef',
        'CoveringDesigns.C20_11_3.low_gram_rank_ge_twelve',
        'CoveringDesigns.C20_11_3.exists_saturated_pair',
        'CoveringDesigns.C20_11_3.saturated_pair_star_eq',
        'CoveringDesigns.C20_11_3.saturated_pair_union',
        'CoveringDesigns.C20_11_3.saturated_pair_inter',
        'CoveringDesigns.C20_11_3.saturated_pair_blocks',
        'CoveringDesigns.C20_11_3.saturated_pair_geometry',
        'CoveringDesigns.C20_11_3.saturated_partner_of_mem',
        'CoveringDesigns.C20_11_3.other_block_eq_complement',
        'CoveringDesigns.C20_11_3.saturated_partner_eq_complement',
        'CoveringDesigns.C20_11_3.saturated_residual_geometry',
        'CoveringDesigns.C20_11_3.mem_onlyBlocks',
        'CoveringDesigns.C20_11_3.mem_neitherBlocks',
        'CoveringDesigns.C20_11_3.onlyBlocks_card_add_pair',
        'CoveringDesigns.C20_11_3.endpoint_sum_partition',
        'CoveringDesigns.C20_11_3.endpoint_card_partition',
        'CoveringDesigns.C20_11_3.trace_sum',
        'CoveringDesigns.C20_11_3.trace_sum_only',
        'CoveringDesigns.C20_11_3.trace_sum_neither',
        'CoveringDesigns.C20_11_3.trace_product_le',
        'CoveringDesigns.C20_11_3.intersection_le_ten',
        'CoveringDesigns.C20_11_3.intersection_sum',
        'CoveringDesigns.C20_11_3.endpoint_degree_partition',
        'CoveringDesigns.C20_11_3.residual_pair_eq',
        'CoveringDesigns.C20_11_3.cross_pair_eq_of_pair_eq',
        'CoveringDesigns.C20_11_3.shared_intersection_sum',
        'CoveringDesigns.C20_11_3.multiplicity_floor_count',
        'CoveringDesigns.C20_11_3.assignment_card_le',
        'CoveringDesigns.C20_11_3.capacity_bound',
        'CoveringDesigns.C20_11_3.capacity_bound_loss16',
        'CoveringDesigns.C20_11_3.cross_count_lower',
        'CoveringDesigns.C20_11_3.no_second_partner_arithmetic',
        'CoveringDesigns.C20_11_3.row_partner_bound',
        'CoveringDesigns.C20_11_3.assignment_card_le_twice',
        'CoveringDesigns.C20_11_3.final_partner_contradiction',
        'CoveringDesigns.C20_11_3.residual_not_mem_other',
        'CoveringDesigns.C20_11_3.cross_partner_exists',
        'CoveringDesigns.C20_11_3.exists_cross_assignment',
        'CoveringDesigns.C20_11_3.endpoint_partner_unique',
        'CoveringDesigns.C20_11_3.saturated_residual_complement',
        'CoveringDesigns.C20_11_3.second_partner_traces_left',
        'CoveringDesigns.C20_11_3.second_partner_trace',
        'CoveringDesigns.C20_11_3.no_saturated_pair_with_degree_six',
        'CoveringDesigns.C20_11_3.no_saturated_pair',
        'CoveringDesigns.lower_bound_20_11_3',
        'CoveringDesigns.knownCover12_20_11_3_card',
        'CoveringDesigns.knownCover12_20_11_3_uniform',
        'CoveringDesigns.knownCover12_20_11_3_covers',
        'CoveringDesigns.knownCover12_20_11_3_isCover',
        'CoveringDesigns.upper_bound_20_11_3',
        'CoveringDesigns.knownCover12_20_11_3_on_card',
        'CoveringDesigns.knownCover12_20_11_3_on_isCover',
        'CoveringDesigns.upper_bound_20_11_3_on',
        'CoveringDesigns.covering_number_20_11_3_on',
        'CoveringDesigns.covering_number_20_11_3',
    ],
    'milestones': [],
    'independent_of': list(['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected']),
    'scope': 'Unconditional C(20,11,3)=12 for ordinary families on arbitrary twenty-point labels: elementary (19,10,2) link bound, degree profile, weighted signless boundary-rank obstruction, and injective actual-block cross-pair counting. Fixed historical twelve-block witness checked by ordinary kernel reduction and transported by relabelling. No classification, enumeration, external certificate or other numerical covering result. Research and formalisation by Rob Gardiner with AI assistance; no claim of a new construction or historical priority.',
}

# Universal structural family, reusing unchanged generic C20 and affine helpers.
COMPONENTS['two-k-minus-two'] = {
    'entry': 'CoveringDesigns.TwoKMinusTwo',
    'audit_name': 'two-k-minus-two-audit',
    'audit_file': 'TwoKMinusTwo.lean',
    'principal_theorem': 'CoveringDesigns.TwoKMinusTwo.exactness',
    'explicit_theorem': 'CoveringDesigns.AuditTwoKMinusTwo.exactness_explicit',
    'summary_path': 'results/two-k-minus-two-verification.json',
    'theorems': [
        'CoveringDesigns.TwoKMinusTwo.product_le_capacity',
        'CoveringDesigns.TwoKMinusTwo.capacity_even',
        'CoveringDesigns.TwoKMinusTwo.capacity_odd',
        'CoveringDesigns.TwoKMinusTwo.capacity_step',
        'CoveringDesigns.TwoKMinusTwo.link_capacity_strict',
        'CoveringDesigns.TwoKMinusTwo.endpoint_budget',
        'CoveringDesigns.TwoKMinusTwo.capacity_twelve_impossible',
        'CoveringDesigns.TwoKMinusTwo.capacity_thirteen_impossible',
        'CoveringDesigns.TwoKMinusTwo.cross_capacity',
        'CoveringDesigns.TwoKMinusTwo.link_lower_bound',
        'CoveringDesigns.TwoKMinusTwo.degree_ge_six',
        'CoveringDesigns.TwoKMinusTwo.pair_ge_two',
        'CoveringDesigns.TwoKMinusTwo.saturated_pair_inter',
        'CoveringDesigns.TwoKMinusTwo.saturated_pair_blocks',
        'CoveringDesigns.TwoKMinusTwo.saturated_pair_geometry',
        'CoveringDesigns.TwoKMinusTwo.saturated_residual_geometry',
        'CoveringDesigns.TwoKMinusTwo.cross_partner_exists',
        'CoveringDesigns.TwoKMinusTwo.exists_cross_assignment',
        'CoveringDesigns.TwoKMinusTwo.excess_nonneg',
        'CoveringDesigns.TwoKMinusTwo.low_row_le',
        'CoveringDesigns.TwoKMinusTwo.low_gram',
        'CoveringDesigns.TwoKMinusTwo.low_card_le',
        'CoveringDesigns.TwoKMinusTwo.conditional_rank',
        'CoveringDesigns.TwoKMinusTwo.endpoint_trace_capacity',
        'CoveringDesigns.TwoKMinusTwo.saturated_capacity',
        'CoveringDesigns.TwoKMinusTwo.saturated_capacity_reduced',
        'CoveringDesigns.TwoKMinusTwo.no_saturation_twelve',
        'CoveringDesigns.TwoKMinusTwo.no_saturation_thirteen',
        'CoveringDesigns.TwoKMinusTwo.thirteen_le_card',
        'CoveringDesigns.TwoKMinusTwo.fourteen_le_card',
        'CoveringDesigns.TwoKMinusTwo.lower_inequality',
        'CoveringDesigns.TwoKMinusTwo.pad_indexed',
        'CoveringDesigns.TwoKMinusTwo.weighted_expansion',
        'CoveringDesigns.TwoKMinusTwo.base_card',
        'CoveringDesigns.TwoKMinusTwo.tetra_card',
        'CoveringDesigns.TwoKMinusTwo.pair_card',
        'CoveringDesigns.TwoKMinusTwo.tetra_not_in_plane',
        'CoveringDesigns.TwoKMinusTwo.tetra_plane_card',
        'CoveringDesigns.TwoKMinusTwo.weight_sum',
        'CoveringDesigns.TwoKMinusTwo.weight_plane_le',
        'CoveringDesigns.TwoKMinusTwo.small_base_subset',
        'CoveringDesigns.TwoKMinusTwo.upper_bound',
        'CoveringDesigns.TwoKMinusTwo.exactness',
        'CoveringDesigns.TwoKMinusTwo.covering_number',
    ],
    'milestones': ['CoveringDesigns.AuditTwoKMinusTwo.lower_explicit',
                   'CoveringDesigns.AuditTwoKMinusTwo.upper_explicit'],
    'independent_of': [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3'] if key not in
        ('affine-constructions', '20-11-3')],
    'scope': 'Ordinary triple covers on arbitrary finite labels: conditional boundary rank, actual-block saturated-pair capacity, unconditional (k+2)b >= 14(k-1) for k>=9, lower bound 13 for k>=20, actual weighted affine covers with at most 14 blocks for k>=3, and exactness 14 for k>=41. Universal polynomial/parity reasoning; empty fibres, smaller projections, padding and deduplication handled. Independent of the numerical C20 result while reusing its unchanged generic incidence and geometry helpers. No native proof assertions, parameter enumeration or search certificates. Historical priority unresolved; research and formalisation by Rob Gardiner with AI assistance.',
}

# Reviewed equality endpoints; all previous proof declarations stay unchanged.
COMPONENTS['two-k-minus-two-equality'] = {
    'entry': 'CoveringDesigns.TwoKMinusTwoEquality',
    'audit_name': 'two-k-minus-two-equality-audit',
    'audit_file': 'TwoKMinusTwoEquality.lean',
    'principal_theorem': 'CoveringDesigns.TwoKMinusTwoEquality.exactness',
    'explicit_theorem': 'CoveringDesigns.AuditTwoKMinusTwoEquality.exactness_explicit',
    'summary_path': 'results/two-k-minus-two-equality-verification.json',
    'theorems': [
        'CoveringDesigns.BoundaryRank.component_pairing',
        'CoveringDesigns.BoundaryRank.gram_equality',
        'CoveringDesigns.TwoKMinusTwoEquality.constant_posSemidef',
        'CoveringDesigns.TwoKMinusTwoEquality.rows_eq_of_gram',
        'CoveringDesigns.TwoKMinusTwoEquality.square_parameters',
        'CoveringDesigns.TwoKMinusTwoEquality.boundary_parameter',
        'CoveringDesigns.TwoKMinusTwoEquality.low_row_sum',
        'CoveringDesigns.TwoKMinusTwoEquality.low_equality_rigidity',
        'CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_low_equality',
        'CoveringDesigns.TwoKMinusTwoEquality.low_count_eq_of_tight',
        'CoveringDesigns.TwoKMinusTwoEquality.card_eleven_of_tight',
        'CoveringDesigns.TwoKMinusTwoEquality.lower_bound_36_19_3',
        'CoveringDesigns.TwoKMinusTwoEquality.lower_bound_78_40_3',
        'CoveringDesigns.TwoKMinusTwoEquality.thirteen_le_card',
        'CoveringDesigns.TwoKMinusTwoEquality.fourteen_le_card',
        'CoveringDesigns.TwoKMinusTwoEquality.exactness',
        'CoveringDesigns.TwoKMinusTwoEquality.covering_number',
        'CoveringDesigns.TwoKMinusTwoEquality.interval_36_19_3_on',
        'CoveringDesigns.TwoKMinusTwoEquality.exactness_78_40_3_on',
    ],
    'milestones': ['CoveringDesigns.AuditTwoKMinusTwoEquality.lower_thirteen_explicit',
                   'CoveringDesigns.AuditTwoKMinusTwoEquality.interval_explicit'],
    'independent_of': [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two'] if key not in
        ('two-k-minus-two', 'affine-constructions', '20-11-3')],
    'scope': 'Reviewed equality refinement for ordinary triple covers on arbitrary finite labels: component equality forces zero deficits and paired rows; square representative margins force eleven blocks. Excludes twelve blocks at (36,19,3) and thirteen at (78,40,3), yielding lower thirteen for k>=19 and exact fourteen for k>=40 with actual attaining families. Reuses unchanged generic C20, family saturation and affine-construction helpers; independent of the numerical C20 proof. The stronger no-high-point classification and threshold optimality are not asserted. Structural proofs only, no native assertions or certificates. Historical priority unresolved; Rob Gardiner with AI assistance.',
}

# Actual-family large-defect composition; earlier components stay unchanged.
COMPONENTS['two-k-minus-c'] = {
    'entry': 'CoveringDesigns.TwoKMinusC',
    'audit_name': 'two-k-minus-c-audit',
    'audit_file': 'TwoKMinusC.lean',
    'principal_theorem': 'CoveringDesigns.TwoKMinusC.OffsetTwo.exactness',
    'explicit_theorem': 'CoveringDesigns.AuditTwoKMinusC.exactness_explicit',
    'summary_path': 'results/two-k-minus-c-verification.json',
    'theorems': [
        'CoveringDesigns.TwoKMinusC.coefficient_zero',
        'CoveringDesigns.TwoKMinusC.coefficient_one',
        'CoveringDesigns.TwoKMinusC.defect_eq',
        'CoveringDesigns.TwoKMinusC.offsetDefect_ge',
        'CoveringDesigns.TwoKMinusC.denominator_pos',
        'CoveringDesigns.TwoKMinusC.value_eq_Q',
        'CoveringDesigns.TwoKMinusC.Q_nonneg',
        'CoveringDesigns.TwoKMinusC.Q_le_iff',
        'CoveringDesigns.TwoKMinusC.ceil_Q_le_iff',
        'CoveringDesigns.TwoKMinusC.actual_subset_floors',
        'CoveringDesigns.TwoKMinusC.actual_floors_bound',
        'CoveringDesigns.TwoKMinusC.actual_floors_real',
        'CoveringDesigns.TwoKMinusC.actual_floors_inequality',
        'CoveringDesigns.TwoKMinusC.Q_two',
        'CoveringDesigns.TwoKMinusC.twelve_lt_Q_two',
        'CoveringDesigns.TwoKMinusC.thirteen_lt_Q_two',
        'CoveringDesigns.TwoKMinusC.OffsetTwo.thirteen_le_card',
        'CoveringDesigns.TwoKMinusC.OffsetTwo.fourteen_le_card',
        'CoveringDesigns.TwoKMinusC.OffsetTwo.exactness',
        'CoveringDesigns.TwoKMinusC.OffsetTwo.covering_number',
        'CoveringDesigns.TwoKMinusC.OffsetTwo.interval_34_18_3_on',
        'CoveringDesigns.TwoKMinusC.OffsetTwo.exactness_70_36_3_on',
    ],
    'milestones': ['CoveringDesigns.AuditTwoKMinusC.lower_thirteen_explicit',
                   'CoveringDesigns.AuditTwoKMinusC.actual_floors_explicit',
                   'CoveringDesigns.AuditTwoKMinusC.occurrence_transport'],
    'independent_of': [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality'] if key not in
        ('two-k-minus-two', 'affine-constructions', '20-11-3',
         'multicover', 'multicover-large-defect', 'multicover-incidence',
         'caro-tuza', 'horsley', 'schoenheim', 'horsley-singh', 'equality',
         'higher-incidence', 'weighted', 'large-defect')],
    'scope': 'Actual point/pair floors six/three in an ordinary uniform family on v+c=2k points, c>=2, c<k and k>6, yield the Horsley-Singh large-defect ratio and ceiling. Generic adapter independent of saturation and numerical endpoints. Separate c=2 compositions give lower thirteen for k>=18 and exact fourteen with arbitrary-label attainment for k>=36. Only 13--14 at (34,18,3). No universal residual floor three, equality refinement, parameter screen or external certificate. Historical priority and threshold optimality unresolved; Rob Gardiner formalisation with AI assistance.',
}

# Reviewed fixed-offset generalisation, separate from the preserved adapter.
COMPONENTS['two-k-minus-c-general'] = {
    'entry': 'CoveringDesigns.TwoKMinusCGeneral',
    'audit_name': 'two-k-minus-c-general-audit',
    'audit_file': 'TwoKMinusCGeneral.lean',
    'principal_theorem': 'CoveringDesigns.TwoKMinusCGeneral.exactness_uniform',
    'explicit_theorem': 'CoveringDesigns.AuditTwoKMinusCGeneral.uniform_explicit',
    'summary_path': 'results/two-k-minus-c-general-verification.json',
    'theorems': [
        'CoveringDesigns.Weighted.partitioned_gram_card_le',
        'CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict',
        'CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible',
        'CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three',
        'CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible',
        'CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment',
        'CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le',
        'CoveringDesigns.TwoKMinusCGeneral.upper_bound',
        'CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity',
        'CoveringDesigns.TwoKMinusCGeneral.saturated_capacity',
        'CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform',
        'CoveringDesigns.TwoKMinusCGeneral.exactness_uniform',
        'CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform',
        'CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three',
        'CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three',
        'CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three',
        'CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on',
        'CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on',
        'CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on',
        'CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card',
        'CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks',
        'CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique',
        'CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists',
        'CoveringDesigns.TwoKMinusCGeneral.link_lower_bound',
        'CoveringDesigns.TwoKMinusCGeneral.degree_ge_six',
        'CoveringDesigns.TwoKMinusCGeneral.pair_ge_two',
        'CoveringDesigns.TwoKMinusCGeneral.Q_three',
        'CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three',
        'CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three',
        'CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast',
        'CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg',
        'CoveringDesigns.TwoKMinusCGeneral.low_row_le',
        'CoveringDesigns.TwoKMinusCGeneral.low_card_le',
        'CoveringDesigns.TwoKMinusCGeneral.conditional_rank',
        'CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform',
        'CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three',
        'CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform',
    ],
    'milestones': ['CoveringDesigns.AuditTwoKMinusCGeneral.three_explicit',
                   'CoveringDesigns.AuditTwoKMinusCGeneral.floors_rank_explicit',
                   'CoveringDesigns.AuditTwoKMinusCGeneral.reduction_transport'],
    'independent_of': [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c'] if key not in
        ('caro-tuza', 'horsley', 'schoenheim', 'horsley-singh', 'equality',
         'higher-incidence', 'weighted', 'large-defect', 'multicover',
         'multicover-incidence', 'multicover-large-defect', 'affine-constructions',
         'point-reduction', '20-11-3', 'two-k-minus-two', 'two-k-minus-c')],
    'scope': 'Reviewed fixed offsets on arbitrary finite labels: exact fourteen for c>=2,k>=25c, and for c=3,k>=59. General link floors and bounded fibres of actual saturated cross-pair assignments give capacity exclusions. Independent integer partition/strict Gram rank yields the uniform lower bound; the preserved actual-floor adapter gives the sharper offset-three composition. Existing affine upper witnesses and ordinary point reduction give actual attainment. No saturation converse, general injectivity, universal residual floor three, equality refinement, numerical C20 result, external certificate or search. Historical priority and threshold optimality unresolved; Rob Gardiner formalisation with AI assistance.',
}

# Support completion preserves all earlier proofs and tightens only two endpoints.
COMPONENTS['two-k-minus-two-tightening'] = {
    'entry': 'CoveringDesigns.TwoKMinusTwoTightening',
    'audit_name': 'two-k-minus-two-tightening-audit',
    'audit_file': 'TwoKMinusTwoTightening.lean',
    'principal_theorem': 'CoveringDesigns.TwoKMinusTwoTightening.exactness',
    'explicit_theorem': 'CoveringDesigns.AuditTwoKMinusTwoTightening.exactness_explicit',
    'summary_path': 'results/two-k-minus-two-tightening-verification.json',
    'theorems': [
        'CoveringDesigns.BoundaryRank.kernel_sum_zero',
        'CoveringDesigns.BoundaryRank.ker_add_constant_eq',
        'CoveringDesigns.BoundaryRank.gram_rank_budget',
        'CoveringDesigns.BoundaryRank.centered_mulVec_one',
        'CoveringDesigns.BoundaryRank.centered_gram',
        'CoveringDesigns.BoundaryRank.centered_rank_eq',
        'CoveringDesigns.BoundaryRank.one_le_corank_of_mulVec_one_eq_zero',
        'CoveringDesigns.BoundaryRank.centered_completion',
        'CoveringDesigns.BoundaryRank.completion_eq_of_corank_le_one',
        'CoveringDesigns.BoundaryRank.binary_completion_eq_or_eq',
        'CoveringDesigns.BoundaryRank.binary_completion_card_le_two',
        'CoveringDesigns.BoundaryRank.completion_card_le_one',
        'CoveringDesigns.BoundaryRank.indexed_pair_sum_of_uniform',
        'CoveringDesigns.BoundaryRank.indexed_clone_capacity_at',
        'CoveringDesigns.BoundaryRank.indexed_clone_capacity',
        'CoveringDesigns.BoundaryRank.indexed_clone_card_le_five',
        'CoveringDesigns.BoundaryRank.indexed_clone_card_le_ten',
        'CoveringDesigns.BoundaryRank.family_clone_capacity',
        'CoveringDesigns.BoundaryRank.clone_card_le_five',
        'CoveringDesigns.BoundaryRank.clone_card_le_ten',
        'CoveringDesigns.BoundaryRank.card_le_mul_image_card',
        'CoveringDesigns.TwoKMinusTwoTightening.lower_bound_32_17_3',
        'CoveringDesigns.TwoKMinusTwoTightening.lower_bound_68_35_3',
        'CoveringDesigns.TwoKMinusTwoTightening.thirteen_le_card',
        'CoveringDesigns.TwoKMinusTwoTightening.fourteen_le_card',
        'CoveringDesigns.TwoKMinusTwoTightening.exactness',
        'CoveringDesigns.TwoKMinusTwoTightening.covering_number',
        'CoveringDesigns.TwoKMinusTwoTightening.interval_32_17_3_on',
        'CoveringDesigns.TwoKMinusTwoTightening.exactness_68_35_3_on',
        'CoveringDesigns.TwoKMinusTwoTightening.low_completion',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_centered_image',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_one',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_supports_le_two',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_five_mul',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_card_le_ten_mul',
        'CoveringDesigns.TwoKMinusTwoTightening.no_twelve_32_17',
        'CoveringDesigns.TwoKMinusTwoTightening.no_thirteen_68_35',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_degree',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_pair',
        'CoveringDesigns.TwoKMinusTwoTightening.supportVector_binary',
        'CoveringDesigns.TwoKMinusTwoTightening.supportVector_sum',
        'CoveringDesigns.TwoKMinusTwoTightening.supportVector_eq_iff',
        'CoveringDesigns.TwoKMinusTwoTightening.low_row_sum',
        'CoveringDesigns.TwoKMinusTwoTightening.supportVector_image',
        'CoveringDesigns.TwoKMinusTwoTightening.high_image',
        'CoveringDesigns.TwoKMinusTwoTightening.low_total_excess',
        'CoveringDesigns.TwoKMinusTwoTightening.deficit_eq_high_sum',
        'CoveringDesigns.TwoKMinusTwoTightening.deficit_sum_le',
        'CoveringDesigns.TwoKMinusTwoTightening.regularHigh_count_bound',
        'CoveringDesigns.TwoKMinusTwoTightening.mem_regularHigh_iff',
    ],
    'milestones': ['CoveringDesigns.AuditTwoKMinusTwoTightening.lower_thirteen_explicit'],
    'independent_of': [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c', 'two-k-minus-c-general'] if key not in
        ('two-k-minus-c', 'two-k-minus-two', 'affine-constructions', '20-11-3',
         'multicover', 'multicover-large-defect', 'multicover-incidence',
         'caro-tuza', 'horsley', 'schoenheim', 'horsley-singh', 'equality',
         'higher-incidence', 'weighted', 'large-defect')],
    'scope': 'Ordinary triple coverings on arbitrary finite labels: lower thirteen at offset two for k>=17 and exact fourteen for k>=35, including attainment; only 13--14 at (32,17,3). Weak nullity, centering, binary support completion and clone capacity exclude the new endpoint budgets with all floors derived internally. Generic centering and completion are finite real-matrix results; clone capacity preserves indexed occurrences. No full component stability classification, equality-refinement dependency, numerical C20 theorem, search or external certificate. Rob Gardiner with AI assistance.',
}

# Arbitrary-corank affine capacity and the k>=33 family, added independently.
COMPONENTS['rank-slack-capacity'] = {
    'entry': 'CoveringDesigns.RankSlackCapacity',
    'audit_name': 'rank-slack-capacity-audit',
    'audit_file': 'RankSlackCapacity.lean',
    'principal_theorem': 'CoveringDesigns.TwoKMinusTwoCapacity.exactness',
    'explicit_theorem': 'CoveringDesigns.AuditRankSlackCapacity.exactness_explicit',
    'summary_path': 'results/rank-slack-capacity-verification.json',
    'theorems': [
        'CoveringDesigns.AffineCapacity.exists_spanning_points',
        'CoveringDesigns.AffineCapacity.coordinate_eq_of_mem_affineSpan',
        'CoveringDesigns.AffineCapacity.row_eq_one_iff',
        'CoveringDesigns.AffineCapacity.common_support_eq',
        'CoveringDesigns.AffineCapacity.exists_block_of_dimension_lt',
        'CoveringDesigns.AffineCapacity.card_le_of_dimension_lt',
        'CoveringDesigns.AffineCapacity.binary_card_le_pow',
        'CoveringDesigns.AffineCapacity.binary_affine_card_le_pow',
        'CoveringDesigns.SupportDimension.one_le_corank',
        'CoveringDesigns.SupportDimension.zeroSumKernel_finrank',
        'CoveringDesigns.SupportDimension.sub_mem_zeroSumKernel',
        'CoveringDesigns.SupportDimension.fibre_eq_translate',
        'CoveringDesigns.SupportDimension.fibre_dimension',
        'CoveringDesigns.SupportDimension.family_dimension_le',
        'CoveringDesigns.SupportDimension.binary_support_card_le',
        'CoveringDesigns.SupportDimension.common_block',
        'CoveringDesigns.SupportCapacity.aggregate',
        'CoveringDesigns.SupportCapacity.signed_aggregate',
        'CoveringDesigns.SupportCapacity.of_support_bound',
        'CoveringDesigns.SupportCapacity.numerator_pos',
        'CoveringDesigns.SupportCapacity.card_le_div_of_support_bound',
        'CoveringDesigns.DeficitCharging.bad_card_le',
        'CoveringDesigns.DeficitCharging.sum_le_mul_positive',
        'CoveringDesigns.DeficitCharging.regular_count',
        'CoveringDesigns.BoundaryIncidence.low_degree',
        'CoveringDesigns.BoundaryIncidence.high_degree',
        'CoveringDesigns.BoundaryIncidence.low_ne_high',
        'CoveringDesigns.BoundaryIncidence.pair_self',
        'CoveringDesigns.BoundaryIncidence.singleton_degree',
        'CoveringDesigns.BoundaryIncidence.pair_comm',
        'CoveringDesigns.BoundaryIncidence.row_binary',
        'CoveringDesigns.BoundaryIncidence.row_sum',
        'CoveringDesigns.BoundaryIncidence.row_dot',
        'CoveringDesigns.BoundaryIncidence.degree_sum',
        'CoveringDesigns.BoundaryIncidence.excess_cast',
        'CoveringDesigns.BoundaryIncidence.total_excess',
        'CoveringDesigns.BoundaryIncidence.balance',
        'CoveringDesigns.BoundaryIncidence.gram',
        'CoveringDesigns.BoundaryIncidence.completion',
        'CoveringDesigns.BoundaryIncidence.degree_balance',
        'CoveringDesigns.BoundaryIncidence.regular_degree',
        'CoveringDesigns.BoundaryIncidence.regular_image',
        'CoveringDesigns.BoundaryIncidence.regular_centered_image',
        'CoveringDesigns.BoundaryIncidence.deficit_le',
        'CoveringDesigns.BoundaryIncidence.regular_count',
        'CoveringDesigns.BoundaryIncidence.lowerCount_le',
        'CoveringDesigns.BoundaryIncidence.row_membership_eq',
        'CoveringDesigns.BoundaryIncidence.supports_le',
        'CoveringDesigns.BoundaryIncidence.dimension_le',
        'CoveringDesigns.BoundaryIncidence.clone_bound',
        'CoveringDesigns.BoundaryIncidence.clone_obstruction',
        'CoveringDesigns.BoundaryIncidence.covering_obstruction',
        'CoveringDesigns.TwoKMinusTwoCapacity.indexed_degree_ge_six',
        'CoveringDesigns.TwoKMinusTwoCapacity.thirteen_budget',
        'CoveringDesigns.TwoKMinusTwoCapacity.no_thirteen',
        'CoveringDesigns.TwoKMinusTwoCapacity.indexed_fourteen_le_card',
        'CoveringDesigns.TwoKMinusTwoCapacity.fourteen_le_card',
        'CoveringDesigns.TwoKMinusTwoCapacity.attaining',
        'CoveringDesigns.TwoKMinusTwoCapacity.exactness',
        'CoveringDesigns.TwoKMinusTwoCapacity.covering_number',
        'CoveringDesigns.C64_33_3.exactness_on',
        'CoveringDesigns.covering_number_64_33_3',
        'CoveringDesigns.C66_34_3.exactness_on',
        'CoveringDesigns.covering_number_66_34_3',
    ],
    'milestones': ['CoveringDesigns.AuditRankSlackCapacity.indexed_explicit'],
    'independent_of': [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c', 'two-k-minus-c-general', 'two-k-minus-two-tightening'] if key not in
        ('two-k-minus-two', 'affine-constructions', '20-11-3',
         'caro-tuza', 'horsley', 'schoenheim', 'horsley-singh', 'equality',
         'higher-incidence', 'weighted', 'large-defect')],
    'scope': 'Actual affine representatives and common-block capacity; arbitrary-corank real fibres and binary support counts; integer charging and signed support-fibre aggregation; actual indexed boundary incidence, weak-nullity selection and two capacities. Every indexed threefold pair cover on 2k-2 points with k>=33 has at least fourteen occurrences, allowing repeated blocks and deriving its own degrees. Ordinary triple-cover exactness at k>=33, with unchanged affine attainment and numerical 64-33-3/66-34-3 corollaries. No component stability, numerical C20 theorem, old tightening/equality proof, search, certificate or new historical-priority claim. Rob Gardiner with AI assistance.',
}

# Additive ordinary endpoint extension and reusable affine/matching machinery.
COMPONENTS['saturated-matching'] = {'entry': 'CoveringDesigns.SaturatedMatching',
 'milestones': [],
 'audit_name': 'saturated-matching-audit',
 'audit_file': 'SaturatedMatching.lean',
 'principal_theorem': 'CoveringDesigns.TwoKMinusTwoMatching.exactness_on',
 'explicit_theorem': 'CoveringDesigns.AuditSaturatedMatching.exactness_explicit',
 'summary_path': 'results/saturated-matching-verification.json',
 'theorems': ['CoveringDesigns.AffineCapacity.affine_coefficients',
              'CoveringDesigns.AffineCapacity.omitted_coordinate',
              'CoveringDesigns.AffineCapacity.omitted_coordinates_rigidity',
              'CoveringDesigns.AffineCapacity.omitted_coordinates_independent',
              'CoveringDesigns.AffineCapacity.boundary_dichotomy',
              'CoveringDesigns.AffineCapacity.boundary_supports',
              'CoveringDesigns.AffineCapacity.card_mul_le_of_dimension_le',
              'CoveringDesigns.AffineCapacity.card_le_max_of_fibres',
              'CoveringDesigns.SaturatedMatching.boundary_six',
              'CoveringDesigns.SaturatedMatching.thirteen_budget',
              'CoveringDesigns.SaturatedMatching.regular_fibre_le_nine',
              'CoveringDesigns.SaturatedMatching.no_thirteen_of_pair_floor',
              'CoveringDesigns.SaturatedMatching.Split.cross_endpoints',
              'CoveringDesigns.SaturatedMatching.Split.matching_endpoints',
              'CoveringDesigns.SaturatedMatching.Split.matching_separate',
              'CoveringDesigns.SaturatedMatching.Split.matching_injective',
              'CoveringDesigns.SaturatedMatching.Split.matching_complete',
              'CoveringDesigns.SaturatedMatching.Split.matching_card',
              'CoveringDesigns.SaturatedMatching.cross_excess_identity',
              'CoveringDesigns.SaturatedMatching.loss_identity',
              'CoveringDesigns.SaturatedMatching.cross_loss_identity',
              'CoveringDesigns.SaturatedMatching.balanced_of_loss_zero',
              'CoveringDesigns.SaturatedMatching.capacity_loss_at',
              'CoveringDesigns.SaturatedMatching.shared_block_bound',
              'CoveringDesigns.SaturatedMatching.assignment_fibre_bound',
              'CoveringDesigns.SaturatedMatching.assignment_total_bound',
              'CoveringDesigns.SaturatedMatching.CoverMatching.cross_card_bound',
              'CoveringDesigns.SaturatedMatching.CoverMatching.four_zero',
              'CoveringDesigns.SaturatedMatching.CoverMatching.cross_exact',
              'CoveringDesigns.SaturatedMatching.Split.balanced_intersections',
              'CoveringDesigns.SaturatedMatching.Split.orient_cross',
              'CoveringDesigns.SaturatedMatching.Split.excess_two',
              'CoveringDesigns.SaturatedMatching.CoverMatching.not_five',
              'CoveringDesigns.SaturatedMatching.Split.residual_of_separated',
              'CoveringDesigns.SaturatedMatching.CoverMatching.four_compatibility',
              'CoveringDesigns.SaturatedMatching.CoverMatching.supporting_intersection_sixteen',
              'CoveringDesigns.SaturatedMatching.CoverMatching.not_four',
              'CoveringDesigns.SaturatedMatching.family_degree',
              'CoveringDesigns.SaturatedMatching.Split.endpoints_left',
              'CoveringDesigns.SaturatedMatching.Split.endpoints_right',
              'CoveringDesigns.SaturatedMatching.Split.complementary',
              'CoveringDesigns.SaturatedMatching.CoverMatching.point_ne',
              'CoveringDesigns.SaturatedMatching.CoverMatching.own_mem',
              'CoveringDesigns.SaturatedMatching.CoverMatching.block_injective',
              'CoveringDesigns.SaturatedMatching.CoverMatching.endpoint_degree',
              'CoveringDesigns.SaturatedMatching.CoverMatching.pair_floor',
              'CoveringDesigns.SaturatedMatching.Split.endpoint_floor',
              'CoveringDesigns.SaturatedMatching.Split.no_second_partner',
              'CoveringDesigns.SaturatedMatching.Split.endpoint_counts',
              'CoveringDesigns.SaturatedMatching.Split.surviving_counts',
              'CoveringDesigns.SaturatedMatching.no_saturation_32',
              'CoveringDesigns.TwoKMinusTwoMatching.fourteen_le_card',
              'CoveringDesigns.TwoKMinusTwoMatching.attaining',
              'CoveringDesigns.TwoKMinusTwoMatching.exactness_on',
              'CoveringDesigns.TwoKMinusTwoMatching.covering_number',
              'CoveringDesigns.SaturatedMatching.five_pair_excess',
              'CoveringDesigns.SaturatedMatching.four_pair_small_intersection',
              'CoveringDesigns.SaturatedMatching.four_rest',
              'CoveringDesigns.SaturatedMatching.Remaining.signatures_compatible',
              'CoveringDesigns.SaturatedMatching.Remaining.no_three_share',
              'CoveringDesigns.SaturatedMatching.Remaining.signature_fibre_le_two',
              'CoveringDesigns.SaturatedMatching.Remaining.two_groups',
              'CoveringDesigns.SaturatedMatching.Remaining.grouped_indices',
              'CoveringDesigns.SaturatedMatching.Remaining.disjoint_correlations',
              'CoveringDesigns.SaturatedMatching.aligned_signs',
              'CoveringDesigns.SaturatedMatching.normalized_from_aligned',
              'CoveringDesigns.SaturatedMatching.normalized_unmatched',
              'CoveringDesigns.SaturatedMatching.normalized_small_intersection',
              'CoveringDesigns.SaturatedMatching.Remaining.exists_of_four',
              'CoveringDesigns.SaturatedMatching.Remaining.point_mem',
              'CoveringDesigns.SaturatedMatching.Remaining.index_ne',
              'CoveringDesigns.SaturatedMatching.Remaining.signature_card',
              'CoveringDesigns.SaturatedMatching.Remaining.pair_count',
              'CoveringDesigns.SaturatedMatching.Remaining.four_pair_count',
              'CoveringDesigns.SaturatedMatching.Remaining.equal_of_missing',
              'CoveringDesigns.SaturatedMatching.Remaining.ne_of_mixed',
              'CoveringDesigns.SaturatedMatching.Remaining.signatures_equal_or_disjoint',
              'CoveringDesigns.SaturatedMatching.Remaining.flip_correlation',
              'CoveringDesigns.SaturatedMatching.Remaining.shared_free_separated',
              'CoveringDesigns.SaturatedMatching.saturated_partner_of_mem',
              'CoveringDesigns.SaturatedMatching.second_partner_block',
              'CoveringDesigns.SaturatedMatching.second_partner_traces_left',
              'CoveringDesigns.SaturatedMatching.second_partner_trace',
              'CoveringDesigns.SaturatedMatching.intersection_le_pred',
              'CoveringDesigns.SaturatedMatching.shared_intersection_sum',
              'CoveringDesigns.SaturatedMatching.Pattern.named_card',
              'CoveringDesigns.SaturatedMatching.Pattern.free_card',
              'CoveringDesigns.SaturatedMatching.Pattern.sum_partition',
              'CoveringDesigns.SaturatedMatching.Pattern.degree_named',
              'CoveringDesigns.SaturatedMatching.Pattern.endpoint_degree',
              'CoveringDesigns.SaturatedMatching.Pattern.five_no_free',
              'CoveringDesigns.SaturatedMatching.Pattern.four_unique_free',
              'CoveringDesigns.SaturatedMatching.Pattern.cross_named_contribution',
              'CoveringDesigns.SaturatedMatching.Pattern.own_named_contribution',
              'CoveringDesigns.SaturatedMatching.Pattern.pair_partition',
              'CoveringDesigns.SaturatedMatching.Pattern.five_pair_multiplicity',
              'CoveringDesigns.SaturatedMatching.Pattern.four_named_lower',
              'CoveringDesigns.SaturatedMatching.Pattern.relabel_degree',
              'CoveringDesigns.SaturatedMatching.Pattern.relabel_pair_floor',
              'CoveringDesigns.SaturatedMatching.Pattern.relabel_named',
              'CoveringDesigns.SaturatedMatching.Remaining.relabel_signature',
              'CoveringDesigns.SaturatedMatching.saturated_matching',
              'CoveringDesigns.SaturatedMatching.Split.loss_le_five',
              'CoveringDesigns.SaturatedMatching.Split.no_internal_left',
              'CoveringDesigns.SaturatedMatching.Split.separates',
              'CoveringDesigns.SaturatedMatching.Split.no_shared_support',
              'CoveringDesigns.SaturatedMatching.Split.cross_disjoint',
              'CoveringDesigns.SaturatedMatching.Split.cross_card_le_four',
              'CoveringDesigns.SaturatedMatching.Split.small_budget',
              'CoveringDesigns.SaturatedMatching.Split.exists_of_saturated',
              'CoveringDesigns.SaturatedMatching.Split.saturated',
              'CoveringDesigns.SaturatedMatching.Split.geometry',
              'CoveringDesigns.SaturatedMatching.Split.weight_left',
              'CoveringDesigns.SaturatedMatching.Split.weight_right',
              'CoveringDesigns.SaturatedMatching.Split.cap_P',
              'CoveringDesigns.SaturatedMatching.Split.cap_Q',
              'CoveringDesigns.SaturatedMatching.Split.cap_N',
              'CoveringDesigns.SaturatedMatching.Split.capacity_bound',
              'CoveringDesigns.SaturatedMatching.Split.cap_sum',
              'CoveringDesigns.SaturatedMatching.Split.parts',
              'CoveringDesigns.SaturatedMatching.Split.assignment',
              'CoveringDesigns.SaturatedMatching.Split.cross_card_le',
              'CoveringDesigns.SaturatedMatching.Split.exact_budget',
              'CoveringDesigns.SaturatedMatching.Split.loss_at',
              'CoveringDesigns.SaturatedMatching.Split.residual_degree_two',
              'CoveringDesigns.SaturatedMatching.Split.refined_bound',
              'CoveringDesigns.SaturatedMatching.Split.swap_P',
              'CoveringDesigns.SaturatedMatching.Split.swap_Q',
              'CoveringDesigns.SaturatedMatching.Split.swap_crosses',
              'CoveringDesigns.SaturatedMatching.no_saturation_31',
              'CoveringDesigns.C60_31_3.no_thirteen',
              'CoveringDesigns.C60_31_3.fourteen_le_card',
              'CoveringDesigns.C60_31_3.attaining',
              'CoveringDesigns.C60_31_3.exactness_on',
              'CoveringDesigns.covering_number_60_31_3',
              'CoveringDesigns.SaturatedMatching.family_pair',
              'CoveringDesigns.C62_32_3.no_thirteen',
              'CoveringDesigns.C62_32_3.fourteen_le_card',
              'CoveringDesigns.C62_32_3.attaining',
              'CoveringDesigns.C62_32_3.exactness_on',
              'CoveringDesigns.covering_number_62_32_3'],
 'independent_of': ['11-5-2',
                    '12-5-2',
                    '12-6-3',
                    '13-7-4',
                    'horsley-lifts',
                    '17-9-5',
                    '47-14-5',
                    '42-15-5',
                    'small-defect',
                    'small-defect-b',
                    'small-defect-c',
                    'coefficient-positivity',
                    'affine-schoenheim',
                    'affine-optimality',
                    'lifting-comparison',
                    'schoenheim-improvement',
                    'multicover-small-defect',
                    'low-degree-selection',
                    'seed-comparison',
                    'exact-design',
                    'point-reduction',
                    'base-affine',
                    'schoenheim-family-comparison',
                    'max-degree-sequence',
                    'max-guarantee',
                    'max-covering',
                    'max-higher-covering',
                    '14-8-5',
                    '59-17-5',
                    '66-18-5',
                    '79-22-5',
                    '87-23-5',
                    '98-22-5',
                    'labelled-cliques',
                    'turan-duality',
                    'turan',
                    'de-caen',
                    'chvatal',
                    'gkp-combination',
                    'gkp-induced',
                    'gkp-induced-averaging',
                    'projective-hyperplanes',
                    'finite-flat-geometry',
                    'degree-selected',
                    'two-k-minus-two-equality',
                    'two-k-minus-c-general'],
 'scope': 'Structural affine-boundary simplex rigidity for actual indexed binary incidence, including '
          'nonuniform blocks and duplicate point supports; exact saturated cross-loss and positive excess, '
          'forced supporting blocks and refined shared-block capacity; independent five-pair and four-pair '
          'compatibility theorems with actual identities and symbolically derived orientations. Ordinary '
          'C(2k-2,k,3)=14 for k>=31, with actual attaining families on arbitrary finite point types and '
          'Fin60/Fin62. The unchanged lower thirteen, k>=33 indexed/ordinary theorem and upper construction '
          'are imported at their stated ranges. The indexed threefold pair scope remains k>=33. No '
          'admissions, extra axioms, search certificate, publication refresh or historical-priority claim. '
          'Rob Gardiner with AI assistance.'}

# Additive C(18,10,3) exactness and reusable restricted equality/support helpers.
COMPONENTS['18-10-3'] = {'entry': 'CoveringDesigns.C18_10_3.SquareSupport',
 'audit_name': 'c18-10-3-audit',
 'audit_file': 'C18_10_3.lean',
 'principal_theorem': 'CoveringDesigns.covering_number_18_10_3_on',
 'explicit_theorem': 'CoveringDesigns.Audit18_10_3.covering_number_explicit',
 'summary_path': 'results/c18-10-3-verification.json',
 'theorems': ['CoveringDesigns.SupportObstruction.exceptional_count',
              'CoveringDesigns.SupportObstruction.paired_support_obstruction',
              'CoveringDesigns.C18_10_3.core_equality',
              'CoveringDesigns.C18_10_3.core_pairing',
              'CoveringDesigns.C18_10_3.core_representatives',
              'CoveringDesigns.C18_10_3.pointSupport_card',
              'CoveringDesigns.C18_10_3.pointSupport_inter',
              'CoveringDesigns.C18_10_3.row_support',
              'CoveringDesigns.C18_10_3.zero_deficit_intersections',
              'CoveringDesigns.C18_10_3.agreeing_high_intersections',
              'CoveringDesigns.C18_10_3.two_high_impossible',
              'CoveringDesigns.C18_10_3.lower_bound_17_9_2',
              'CoveringDesigns.C18_10_3.degree_ge_six',
              'CoveringDesigns.C18_10_3.pair_ge_two',
              'CoveringDesigns.C18_10_3.eleven_le_card',
              'CoveringDesigns.C18_10_3.degree_excess_sum',
              'CoveringDesigns.C18_10_3.degree_bounds',
              'CoveringDesigns.C18_10_3.degree_profiles',
              'CoveringDesigns.C18_10_3.outside_card',
              'CoveringDesigns.C18_10_3.pair_self',
              'CoveringDesigns.C18_10_3.pair_sum_all',
              'CoveringDesigns.C18_10_3.sum_outside',
              'CoveringDesigns.C18_10_3.row_gram_entry',
              'CoveringDesigns.C18_10_3.row_binary',
              'CoveringDesigns.C18_10_3.row_sum',
              'CoveringDesigns.C18_10_3.row_gram',
              'CoveringDesigns.C18_10_3.rowExcess_symm',
              'CoveringDesigns.C18_10_3.rowExcess_nonneg',
              'CoveringDesigns.C18_10_3.rowExcess_diag',
              'CoveringDesigns.C18_10_3.rowDeficit_add',
              'CoveringDesigns.C18_10_3.row_balance',
              'CoveringDesigns.C18_10_3.rowDeficit_le_three',
              'CoveringDesigns.C18_10_3.deficit_total_identity',
              'CoveringDesigns.C18_10_3.low_zero_bound',
              'CoveringDesigns.lower_bound_18_10_3',
              'CoveringDesigns.indexed_lower_bound_18_10_3',
              'CoveringDesigns.C18_10_3.deficit_zero_budget',
              'CoveringDesigns.C18_10_3.one_high_impossible',
              'CoveringDesigns.C18_10_3.high_supports_equal',
              'CoveringDesigns.C18_10_3.two_high_deficit_total',
              'CoveringDesigns.C18_10_3.high_seven_deficits',
              'CoveringDesigns.C18_10_3.high_pair_eq_six',
              'CoveringDesigns.C18_10_3.saturated_degree_sum',
              'CoveringDesigns.C18_10_3.saturated_low_endpoint',
              'CoveringDesigns.C18_10_3.saturated_local',
              'CoveringDesigns.C18_10_3.pair_filter',
              'CoveringDesigns.C18_10_3.mem_saturatedEdges_pair',
              'CoveringDesigns.C18_10_3.edge_cases',
              'CoveringDesigns.C18_10_3.edge_partner',
              'CoveringDesigns.C18_10_3.saturated_endpoints',
              'CoveringDesigns.C18_10_3.saturated_no_second',
              'CoveringDesigns.C18_10_3.edges_disjoint',
              'CoveringDesigns.C18_10_3.edges_card_le_eight',
              'CoveringDesigns.C18_10_3.all_other_edges_cross',
              'CoveringDesigns.C18_10_3.supporting_index_unique',
              'CoveringDesigns.C18_10_3.no_saturated_pair',
              'CoveringDesigns.C18_10_3.pair_ge_three',
              'CoveringDesigns.knownBlocks12_18_10_3_distinct',
              'CoveringDesigns.knownCover12_18_10_3_card',
              'CoveringDesigns.knownCover12_18_10_3_uniform',
              'CoveringDesigns.knownCover12_18_10_3_covers',
              'CoveringDesigns.knownCover12_18_10_3_isCover',
              'CoveringDesigns.upper_bound_18_10_3',
              'CoveringDesigns.knownCover12_18_10_3_on_card',
              'CoveringDesigns.knownCover12_18_10_3_on_isCover',
              'CoveringDesigns.upper_bound_18_10_3_on',
              'CoveringDesigns.covering_number_18_10_3_on',
              'CoveringDesigns.covering_number_18_10_3',
              'CoveringDesigns.BoundaryRank.restricted_component_pairing',
              'CoveringDesigns.BoundaryRank.restricted_kernel_pairing',
              'CoveringDesigns.BoundaryRank.square_duality',
              'CoveringDesigns.BoundaryRank.binary_sum',
              'CoveringDesigns.BoundaryRank.binary_dot',
              'CoveringDesigns.BoundaryRank.two_zero_rows',
              'CoveringDesigns.BoundaryRank.exceptional_support',
              'CoveringDesigns.SupportObstruction.intersection_identity',
              'CoveringDesigns.SupportObstruction.empty_of_intersection_bound',
              'CoveringDesigns.SupportObstruction.uncovered_triple',
              'CoveringDesigns.SupportObstruction.single_differences',
              'CoveringDesigns.SupportObstruction.intersections_eq_of_agree',
              'CoveringDesigns.SupportObstruction.empty_of_subtraction_bound',
              'CoveringDesigns.IncidencePacking.packing'],
 'milestones': ['CoveringDesigns.Audit18_10_3.indexed_explicit',
                'CoveringDesigns.Audit18_10_3.core_equality_explicit'],
 'independent_of': ['caro-tuza',
                    'horsley',
                    'schoenheim',
                    '11-5-2',
                    '12-5-2',
                    '12-6-3',
                    '13-7-4',
                    'horsley-lifts',
                    'horsley-singh',
                    'equality',
                    '17-9-5',
                    'higher-incidence',
                    'weighted',
                    '47-14-5',
                    '42-15-5',
                    'large-defect',
                    'small-defect',
                    'small-defect-b',
                    'small-defect-c',
                    'multicover',
                    'multicover-incidence',
                    'multicover-large-defect',
                    'coefficient-positivity',
                    'affine-constructions',
                    'affine-schoenheim',
                    'affine-optimality',
                    'lifting-comparison',
                    'schoenheim-improvement',
                    'multicover-small-defect',
                    'low-degree-selection',
                    'seed-comparison',
                    'exact-design',
                    'point-reduction',
                    'base-affine',
                    'schoenheim-family-comparison',
                    'max-degree-sequence',
                    'max-guarantee',
                    'max-covering',
                    'max-higher-covering',
                    '14-8-5',
                    '59-17-5',
                    '66-18-5',
                    '79-22-5',
                    '87-23-5',
                    '98-22-5',
                    'labelled-cliques',
                    'turan-duality',
                    'turan',
                    'de-caen',
                    'chvatal',
                    'gkp-combination',
                    'gkp-induced',
                    'gkp-induced-averaging',
                    'projective-hyperplanes',
                    'finite-flat-geometry',
                    'degree-selected',
                    'two-k-minus-c',
                    'two-k-minus-c-general',
                    'two-k-minus-two-tightening',
                    'rank-slack-capacity'],
 'scope': 'Unconditional C(18,10,3)=12 on arbitrary finite point labels; historical twelve-block '
          'witness checked by the Lean kernel, with repeated-occurrence lower-bound adapter. '
          'Direct paired-support incidence obstruction and restricted-kernel equality; '
          'retained square-support interfaces are compiled for their audits, outside the covering '
          'proof import route. No diagnostic matrix, classification, external certificate or new '
          'historical-priority claim. Rob Gardiner with AI assistance.'}

# Five standard lifting consequences of one independently verified structural seed.
COMPONENTS['c18103-lifts'] = {
    'entry': 'CoveringDesigns.Applications.C18103Lifts',
    'audit_name': 'c18103-lifts-audit',
    'audit_file': 'C18103Lifts.lean',
    'explicit_theorem': 'CoveringDesigns.AuditC18103Lifts.lower_bound_23_15_8_explicit',
    'principal_theorem': 'CoveringDesigns.Applications.C18103Lifts.lower_bound_23_15_8',
    'summary_path': 'results/c18103-lifts-verification.json',
    'theorems': ['CoveringDesigns.Applications.C18103Lifts.lower_bound', 'CoveringDesigns.Applications.C18103Lifts.ceilings', 'CoveringDesigns.Applications.C18103Lifts.lower_bound_19_11_4', 'CoveringDesigns.Applications.C18103Lifts.lower_bound_20_12_5', 'CoveringDesigns.Applications.C18103Lifts.lower_bound_21_13_6', 'CoveringDesigns.Applications.C18103Lifts.lower_bound_22_14_7', 'CoveringDesigns.Applications.C18103Lifts.lower_bound_23_15_8'],
    'milestones': ['CoveringDesigns.AuditC18103Lifts.lower_bound_19_11_4_explicit', 'CoveringDesigns.AuditC18103Lifts.lower_bound_20_12_5_explicit', 'CoveringDesigns.AuditC18103Lifts.lower_bound_21_13_6_explicit', 'CoveringDesigns.AuditC18103Lifts.lower_bound_22_14_7_explicit'],
    'independent_of': ['11-5-2', '12-5-2', '12-6-3', '13-7-4',
                       'horsley-lifts', 'labelled-cliques', 'finite-flat-geometry'],
    'scope': 'Ordinary arbitrary-label lower bounds 21,35,57,90,138 for (19,11,4) '
             'through (23,15,8), retaining every intermediate ceiling from the '
             'unconditional C(18,10,3) seed. Standard Schoenheim consequences; '
             'no supplied seed hypothesis, new lifting foundation or higher exactness claim.',
}

# Structural C(14,5,3) interval; separately named modules and audits.
COMPONENTS['14-5-3'] = {'entry': 'CoveringDesigns.C14_5_3.Examples',
 'audit_name': 'c14-5-3-audit',
 'audit_file': 'C14_5_3.lean',
 'principal_theorem': 'CoveringDesigns.covering_interval_14_5_3_on',
 'explicit_theorem': 'CoveringDesigns.Audit14_5_3.covering_interval_explicit',
 'summary_path': 'results/c14-5-3-verification.json',
 'theorems': ['CoveringDesigns.C14_5_3.linkPairExcess_self',
              'CoveringDesigns.C14_5_3.linkPairExcess_comm',
              'CoveringDesigns.C14_5_3.pair_link_point_floor',
              'CoveringDesigns.C14_5_3.link_excess_sum',
              'CoveringDesigns.C14_5_3.link_excess_row',
              'CoveringDesigns.C14_5_3.link_pair_excess_zero',
              'CoveringDesigns.C14_5_3.high_excess_sum',
              'CoveringDesigns.C14_5_3.high_excess_row',
              'CoveringDesigns.C14_5_3.high_excess_pos',
              'CoveringDesigns.C14_5_3.pair_support_union',
              'CoveringDesigns.C14_5_3.high_points_card',
              'CoveringDesigns.C14_5_3.high_degree_five',
              'CoveringDesigns.C14_5_3.low_degree_four',
              'CoveringDesigns.C14_5_3.low_pair_exact',
              'CoveringDesigns.C14_5_3.almost_small_intersections',
              'CoveringDesigns.C14_5_3.almost_intersection_sum',
              'CoveringDesigns.C14_5_3.small_intersection_balance',
              'CoveringDesigns.C14_5_3.one_high_meets_all',
              'CoveringDesigns.C14_5_3.low_block_unique_disjoint',
              'CoveringDesigns.C14_5_3.one_high_pair_two',
              'CoveringDesigns.C14_5_3.four_point_regular',
              'CoveringDesigns.C14_5_3.high_pair_excess_one',
              'CoveringDesigns.C14_5_3.almost_pair_profile',
              'CoveringDesigns.C14_5_3.almost_high_block',
              'CoveringDesigns.C14_5_3.delete_index_balance',
              'CoveringDesigns.C14_5_3.almost_exact_deletion',
              'CoveringDesigns.C14_5_3.subset_filter_powerset',
              'CoveringDesigns.C14_5_3.low_pair_exact_of_not_subset',
              'CoveringDesigns.C14_5_3.high_pair_sum',
              'CoveringDesigns.C14_5_3.bounded_fiber_sum',
              'CoveringDesigns.C14_5_3.high_trace_moments',
              'CoveringDesigns.C14_5_3.exists_one_high_block',
              'CoveringDesigns.C14_5_3.exists_low_block_of_no_high_block',
              'CoveringDesigns.C14_5_3.collinearCount_pos',
              'CoveringDesigns.C14_5_3.collinear_sum',
              'CoveringDesigns.C14_5_3.triple_sum_split',
              'CoveringDesigns.C14_5_3.completion_slack',
              'CoveringDesigns.C14_5_3.completion_capacity',
              'CoveringDesigns.C14_5_3.completion_equality',
              'CoveringDesigns.C14_5_3.collinear_pair_count',
              'CoveringDesigns.C14_5_3.noncollinear_pair_count',
              'CoveringDesigns.C14_5_3.completion_pair_identity',
              'CoveringDesigns.C14_5_3.extensions_inside_pair',
              'CoveringDesigns.C14_5_3.collinear_extensions_eq',
              'CoveringDesigns.C14_5_3.line_pair_sum',
              'CoveringDesigns.C14_5_3.linewise_divisibility',
              'CoveringDesigns.C14_5_3.completion_at_least_27',
              'CoveringDesigns.C14_5_3.completed_uniform',
              'CoveringDesigns.C14_5_3.completed_covers_new',
              'CoveringDesigns.C14_5_3.completed_covers_collinear',
              'CoveringDesigns.C14_5_3.completed_covers_noncollinear',
              'CoveringDesigns.C14_5_3.completed_isCover',
              'CoveringDesigns.C14_5_3.completion_at_least_28',
              'CoveringDesigns.C14_5_3.block_charge_capacity',
              'CoveringDesigns.C14_5_3.block_charge_five',
              'CoveringDesigns.C14_5_3.block_charge_eight',
              'CoveringDesigns.C14_5_3.disjoint_charge_budget',
              'CoveringDesigns.C14_5_3.exact_line_count',
              'CoveringDesigns.C14_5_3.exact_point_count',
              'CoveringDesigns.C14_5_3.exact_unique_line',
              'CoveringDesigns.C14_5_3.exact_line_intersection',
              'CoveringDesigns.C14_5_3.exact_multiplicity_le_one',
              'CoveringDesigns.C14_5_3.exact_lines_injective',
              'CoveringDesigns.C14_5_3.exact_lines_meet',
              'CoveringDesigns.C14_5_3.collinear_card',
              'CoveringDesigns.C14_5_3.noncollinear_card',
              'CoveringDesigns.C14_5_3.degree_through_point',
              'CoveringDesigns.C14_5_3.no_five_arc',
              'CoveringDesigns.C14_5_3.Boundary.repeated_cover',
              'CoveringDesigns.C14_5_3.Boundary.repeated_not_irredundant',
              'CoveringDesigns.C14_5_3.Boundary.delete_one_still_covers',
              'CoveringDesigns.C14_5_3.Boundary.delete_all_copies_fails',
              'CoveringDesigns.C14_5_3.Boundary.deletion_counts_one_occurrence',
              'CoveringDesigns.C14_5_3.Boundary.almost_exact_without_injectivity',
              'CoveringDesigns.C14_5_3.Boundary.forty_private_without_structural_premises',
              'CoveringDesigns.C14_5_3.exact_of_capacity',
              'CoveringDesigns.C14_5_3.point_floor',
              'CoveringDesigns.C14_5_3.pair_floor',
              'CoveringDesigns.C14_5_3.minimum_link_exact',
              'CoveringDesigns.C14_5_3.residual_card',
              'CoveringDesigns.C14_5_3.residual_uniform',
              'CoveringDesigns.C14_5_3.residual_completion',
              'CoveringDesigns.C14_5_3.lower_bound_40',
              'CoveringDesigns.C14_5_3.forty_irredundant',
              'CoveringDesigns.C14_5_3.Irredundant.injective',
              'CoveringDesigns.C14_5_3.Irredundant.private_multiplicity',
              'CoveringDesigns.C14_5_3.tight_extensions',
              'CoveringDesigns.C14_5_3.minimum_pair_exact',
              'CoveringDesigns.C14_5_3.minimum_triple_exact',
              'CoveringDesigns.C14_5_3.selected_trace_count',
              'CoveringDesigns.C14_5_3.trace_complement_card',
              'CoveringDesigns.C14_5_3.four_minimum_forces_sixteen',
              'CoveringDesigns.C14_5_3.multiplicity_mono',
              'CoveringDesigns.C14_5_3.multiplicity_pos_iff',
              'CoveringDesigns.C14_5_3.multiplicity_one_iff',
              'CoveringDesigns.C14_5_3.multiplicity_ge_two',
              'CoveringDesigns.C14_5_3.trace_count',
              'CoveringDesigns.C14_5_3.intersection_sum',
              'CoveringDesigns.C14_5_3.selected_subset_count',
              'CoveringDesigns.C14_5_3.restrict_multiplicity',
              'CoveringDesigns.C14_5_3.restrict_add_complement',
              'CoveringDesigns.C14_5_3.forty_has_minimum',
              'CoveringDesigns.C14_5_3.degree_profile_bound',
              'CoveringDesigns.C14_5_3.not_forty',
              'CoveringDesigns.C14_5_3.indexed_lower_bound',
              'CoveringDesigns.C14_5_3.lower_bound',
              'CoveringDesigns.C14_5_3.minimum_pair_trace_sum',
              'CoveringDesigns.C14_5_3.no_five_minimum',
              'CoveringDesigns.C14_5_3.minimum_points_le_four',
              'CoveringDesigns.C14_5_3.four_minimum_frame',
              'CoveringDesigns.C14_5_3.missed_minimum_triple',
              'CoveringDesigns.C14_5_3.minimum_trace_restriction',
              'CoveringDesigns.C14_5_3.minimum_frame',
              'CoveringDesigns.C14_5_3.minimum_trace_moments',
              'CoveringDesigns.C14_5_3.frame_trace_counts',
              'CoveringDesigns.C14_5_3.containing_trace_sum',
              'CoveringDesigns.C14_5_3.subtype_map_subset',
              'CoveringDesigns.C14_5_3.subtype_values_multiplicity',
              'CoveringDesigns.C14_5_3.residual_multiplicity_split',
              'CoveringDesigns.C14_5_3.residual_specials_card',
              'CoveringDesigns.C14_5_3.residual_marks_nonempty',
              'CoveringDesigns.C14_5_3.residual_charges_disjoint',
              'CoveringDesigns.C14_5_3.residual_charge_excess',
              'CoveringDesigns.C14_5_3.residual_marks_card',
              'CoveringDesigns.C14_5_3.special_charge_eight',
              'CoveringDesigns.C14_5_3.minimum_special_count',
              'CoveringDesigns.C14_5_3.without_point_card',
              'CoveringDesigns.C14_5_3.insert_without_point',
              'CoveringDesigns.C14_5_3.link_parent_multiplicity',
              'CoveringDesigns.C14_5_3.without_point_subset_iff',
              'CoveringDesigns.C14_5_3.exists_special',
              'CoveringDesigns.C14_5_3.SpecialAt.duplicate',
              'CoveringDesigns.C14_5_3.special_blocks_equal',
              'CoveringDesigns.C14_5_3.special_avoids_minimum',
              'CoveringDesigns.C14_5_3.mem_specialIndices',
              'CoveringDesigns.C14_5_3.special_at_member',
              'CoveringDesigns.C14_5_3.special_group_unique',
              'CoveringDesigns.C14_5_3.private_high',
              'CoveringDesigns.C14_5_3.special_middle_le_two',
              'CoveringDesigns.C14_5_3.selected_intersection_sum',
              'CoveringDesigns.C14_5_3.special_group_count',
              'CoveringDesigns.C14_5_3.middle_le_twice_special',
              'CoveringDesigns.C14_5_3.distinct_private_triples',
              'CoveringDesigns.knownBlocks43_14_5_3_distinct',
              'CoveringDesigns.knownCover43_14_5_3_card',
              'CoveringDesigns.knownCover43_14_5_3_uniform',
              'CoveringDesigns.knownCover43_14_5_3_covers',
              'CoveringDesigns.knownCover43_14_5_3_isCover',
              'CoveringDesigns.upper_bound_14_5_3',
              'CoveringDesigns.knownCover43_14_5_3_on_card',
              'CoveringDesigns.knownCover43_14_5_3_on_isCover',
              'CoveringDesigns.upper_bound_14_5_3_on',
              'CoveringDesigns.lower_bound_14_5_3',
              'CoveringDesigns.indexed_lower_bound_14_5_3',
              'CoveringDesigns.covering_interval_14_5_3_on',
              'CoveringDesigns.covering_interval_14_5_3'],
 'milestones': ['CoveringDesigns.Audit14_5_3.indexed_explicit',
                'CoveringDesigns.Audit14_5_3.completion_explicit'],
 'scope': 'Unconditional interval 41 <= C(14,5,3) <= 43 on arbitrary finite labels; indexed repetitions '
          'permitted. Structural exact-link completion27 precedes lower40, irredundancy and exclusion40; '
          'completion28 is downstream. Self-contained order-three deletion special case, with Sane '
          'antecedent credited; historical Nurmela-Ostergard witness kernel checked. No classification, '
          'external exclusion certificate, exactness or first-discovery claim. Rob Gardiner with AI '
          'assistance.'}
COMPONENTS['14-5-3']['independent_of'] = [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c', 'two-k-minus-c-general', 'two-k-minus-two-tightening', 'rank-slack-capacity', 'saturated-matching', '18-10-3', 'c18103-lifts', '14-5-3'] if key not in
    ('14-5-3', 'schoenheim', 'horsley-singh', 'multicover', 'exact-design', 'labelled-cliques')]

# One shared quadruple assembly, its six witnesses and two small base cases.
COMPONENTS['quadruple-assembly'] = {'entry': 'CoveringDesigns.QuadrupleAssembly',
 'audit_name': 'quadruple-assembly-audit',
 'audit_file': 'QuadrupleAssembly.lean',
 'principal_theorem': 'CoveringDesigns.QuadrupleAssembly.assembly_optimal',
 'explicit_theorem': 'CoveringDesigns.AuditQuadrupleAssembly.assembly_explicit',
 'summary_path': 'results/quadruple-assembly-verification.json',
 'theorems': ['CoveringDesigns.QuadrupleAssembly.assembly_optimal',
              'CoveringDesigns.QuadrupleAssembly.assembly_sharp',
              'CoveringDesigns.QuadrupleAssembly.sources_injective',
              'CoveringDesigns.QuadrupleAssembly.classes_disjoint',
              'CoveringDesigns.QuadrupleAssembly.ceilings',
              'CoveringDesigns.QuadrupleAssembly.lower_bound',
              'CoveringDesigns.QuadrupleAssembly.h_seed_card',
              'CoveringDesigns.QuadrupleAssembly.gdd_seed_card',
              'CoveringDesigns.QuadrupleAssembly.h_valid',
              'CoveringDesigns.QuadrupleAssembly.g_valid',
              'CoveringDesigns.QuadrupleAssembly.filling_valid',
              'CoveringDesigns.QuadrupleAssembly.filling_card',
              'CoveringDesigns.QuadrupleAssembly.factors_valid',
              'CoveringDesigns.QuadrupleAssembly.label_some',
              'CoveringDesigns.QuadrupleAssembly.productSubstitute_valid',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V37.rows_eq',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V37.correspondence',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V37.optimal',
              'CoveringDesigns.knownCover1998_37_4_3_optimal',
              'CoveringDesigns.knownCover1998_37_4_3_on_optimal',
              'CoveringDesigns.lower_bound_37_4_3',
              'CoveringDesigns.covering_number_37_4_3_on',
              'CoveringDesigns.covering_number_37_4_3',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V49.rows_eq',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V49.correspondence',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V49.optimal',
              'CoveringDesigns.knownCover4704_49_4_3_optimal',
              'CoveringDesigns.knownCover4704_49_4_3_on_optimal',
              'CoveringDesigns.lower_bound_49_4_3',
              'CoveringDesigns.covering_number_49_4_3_on',
              'CoveringDesigns.covering_number_49_4_3',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V61.rows_eq',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V61.correspondence',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V61.optimal',
              'CoveringDesigns.knownCover9150_61_4_3_optimal',
              'CoveringDesigns.knownCover9150_61_4_3_on_optimal',
              'CoveringDesigns.lower_bound_61_4_3',
              'CoveringDesigns.covering_number_61_4_3_on',
              'CoveringDesigns.covering_number_61_4_3',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V73.rows_eq',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V73.correspondence',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V73.optimal',
              'CoveringDesigns.knownCover15768_73_4_3_optimal',
              'CoveringDesigns.knownCover15768_73_4_3_on_optimal',
              'CoveringDesigns.lower_bound_73_4_3',
              'CoveringDesigns.covering_number_73_4_3_on',
              'CoveringDesigns.covering_number_73_4_3',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V85.rows_eq',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V85.correspondence',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V85.optimal',
              'CoveringDesigns.knownCover24990_85_4_3_optimal',
              'CoveringDesigns.knownCover24990_85_4_3_on_optimal',
              'CoveringDesigns.lower_bound_85_4_3',
              'CoveringDesigns.covering_number_85_4_3_on',
              'CoveringDesigns.covering_number_85_4_3',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V97.rows_eq',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V97.correspondence',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V97.optimal',
              'CoveringDesigns.knownCover37248_97_4_3_optimal',
              'CoveringDesigns.knownCover37248_97_4_3_on_optimal',
              'CoveringDesigns.lower_bound_97_4_3',
              'CoveringDesigns.covering_number_97_4_3_on',
              'CoveringDesigns.covering_number_97_4_3',
              'CoveringDesigns.QuadrupleAssembly.ceilings_13',
              'CoveringDesigns.QuadrupleAssembly.ceilings_25',
              'CoveringDesigns.QuadrupleAssembly.schoenheim_13',
              'CoveringDesigns.QuadrupleAssembly.schoenheim_25',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V25.checked',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V25.valid',
              'CoveringDesigns.QuadrupleAssembly.WitnessData.V25.size',
              'CoveringDesigns.knownCover78_13_4_3_correspondence',
              'CoveringDesigns.knownCover78_13_4_3_optimal',
              'CoveringDesigns.knownCover78_13_4_3_on_optimal',
              'CoveringDesigns.lower_bound_13_4_3',
              'CoveringDesigns.covering_number_13_4_3_on',
              'CoveringDesigns.covering_number_13_4_3',
              'CoveringDesigns.knownCover600_25_4_3_correspondence',
              'CoveringDesigns.knownCover600_25_4_3_optimal',
              'CoveringDesigns.knownCover600_25_4_3_on_optimal',
              'CoveringDesigns.lower_bound_25_4_3',
              'CoveringDesigns.covering_number_25_4_3_on',
              'CoveringDesigns.covering_number_25_4_3',
              'CoveringDesigns.QuadrupleAssembly.admissible_below_100_iff',
              'CoveringDesigns.QuadrupleAssembly.formula_divisible_below_100',
              'CoveringDesigns.covering_number_one_mod_twelve_below_100_on',
              'CoveringDesigns.covering_number_one_mod_twelve_below_100'],
 'milestones': ['CoveringDesigns.AuditQuadrupleAssembly.exact_37_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_49_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_61_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_73_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_85_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_97_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_13_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.exact_25_explicit',
                'CoveringDesigns.AuditQuadrupleAssembly.finite_range_explicit'],
 'scope': 'Direct even-case HMM adaptation, actual ordinary-family assembly, kernel-checked small bases and '
          'structural substitution, two small exact base cases and an unconditional eight-case theorem '
          'for admissible orders congruent to one mod twelve below 100. Named families are lossless '
          'projections of the six preserved witnesses, reused thirteen-point filling and recovered '
          'historical twenty-five-point file. Rob Gardiner with AI assistance; LJCR-derived data '
          'retain Daniel M. Gordon/LJCR CC BY 4.0 credit. No all-order seed-existence or new-discovery '
          'claim.'}
COMPONENTS['quadruple-assembly']['independent_of'] = [key for key in ['caro-tuza', 'horsley', 'schoenheim', '11-5-2', '12-5-2', '12-6-3', '13-7-4', 'horsley-lifts', 'horsley-singh', 'equality', '17-9-5', 'higher-incidence', 'weighted', '47-14-5', '42-15-5', 'large-defect', 'small-defect', 'small-defect-b', 'small-defect-c', 'multicover', 'multicover-incidence', 'multicover-large-defect', 'coefficient-positivity', 'affine-constructions', 'affine-schoenheim', 'affine-optimality', 'lifting-comparison', 'schoenheim-improvement', 'multicover-small-defect', 'low-degree-selection', 'seed-comparison', 'exact-design', 'point-reduction', 'base-affine', 'schoenheim-family-comparison', 'max-degree-sequence', 'max-guarantee', 'max-covering', 'max-higher-covering', '14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5', 'labelled-cliques', 'turan-duality', 'turan', 'de-caen', 'chvatal', 'gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'finite-flat-geometry', 'degree-selected', '20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c', 'two-k-minus-c-general', 'two-k-minus-two-tightening', 'rank-slack-capacity', 'saturated-matching', '18-10-3', 'c18103-lifts', '14-5-3', 'quadruple-assembly'] if key not in ('quadruple-assembly', 'schoenheim')]


# Six assessed consequences, preserving all earlier proof modules and contracts.
C1453_LIFT_KEYS = ('15-6-4', '16-7-5', '17-8-6', '18-9-7', '19-10-8')
COMPONENTS.update({
    '34-18-3': {
        "entry": "CoveringDesigns.C34_18_3",
        "audit_name": "c34-18-3-audit",
        "audit_file": "C34_18_3.lean",
        "principal_theorem": "CoveringDesigns.covering_number_34_18_3_on",
        "explicit_theorem": "CoveringDesigns.Audit34_18_3.covering_number_explicit",
        "summary_path": "results/c34-18-3-verification.json",
        "theorems": [
            "CoveringDesigns.knownBlocks13_34_18_3_distinct",
            "CoveringDesigns.knownCover13_34_18_3_card",
            "CoveringDesigns.knownCover13_34_18_3_uniform",
            "CoveringDesigns.knownCover13_34_18_3_covers",
            "CoveringDesigns.knownCover13_34_18_3_isCover",
            "CoveringDesigns.upper_bound_34_18_3",
            "CoveringDesigns.knownCover13_34_18_3_on_card",
            "CoveringDesigns.knownCover13_34_18_3_on_isCover",
            "CoveringDesigns.upper_bound_34_18_3_on",
            "CoveringDesigns.lower_bound_34_18_3",
            "CoveringDesigns.covering_number_34_18_3_on",
            "CoveringDesigns.covering_number_34_18_3"
        ],
        "milestones": [],
        "independent_of": [
            "11-5-2",
            "12-5-2",
            "12-6-3",
            "13-7-4",
            "14-5-3",
            "15-6-4",
            "16-7-5",
            "17-8-6",
            "18-9-7",
            "19-10-8",
            "quadruple-assembly"
        ],
        "scope": "Exact C(34,18,3)=13 on arbitrary finite labels. The preserved unconditional offset-two theorem supplies lower thirteen; ordinary kernel reduction verifies the historical LJCR multiple of (17,9,3), recorded in 2009, with thirteen distinct blocks. No new construction or historical-priority claim."
    },
    '15-6-4': {
        "entry": "CoveringDesigns.C15_6_4",
        "audit_name": "c15-6-4-audit",
        "audit_file": "C15_6_4.lean",
        "principal_theorem": "CoveringDesigns.lower_bound_15_6_4",
        "explicit_theorem": "CoveringDesigns.Audit15_6_4.lower_bound_explicit",
        "summary_path": "results/c15-6-4-verification.json",
        "theorems": [
            "CoveringDesigns.lower_bound_15_6_4"
        ],
        "milestones": [],
        "independent_of": [
            "11-5-2",
            "12-5-2",
            "12-6-3",
            "13-7-4",
            "18-10-3",
            "c18103-lifts",
            "34-18-3",
            "quadruple-assembly"
        ],
        "scope": "Universal ordinary C(15,6,4) >= 103, by direct Schoenheim lifting of the universal 41 lower bound at (14,5,3). A consequence of the existing C(14,5,3)>=41 proof, retaining every ceiling. No supplied seed hypothesis, new mechanism or exactness claim."
    },
    '16-7-5': {
        "entry": "CoveringDesigns.C16_7_5",
        "audit_name": "c16-7-5-audit",
        "audit_file": "C16_7_5.lean",
        "principal_theorem": "CoveringDesigns.lower_bound_16_7_5",
        "explicit_theorem": "CoveringDesigns.Audit16_7_5.lower_bound_explicit",
        "summary_path": "results/c16-7-5-verification.json",
        "theorems": [
            "CoveringDesigns.lower_bound_16_7_5"
        ],
        "milestones": [],
        "independent_of": [
            "11-5-2",
            "12-5-2",
            "12-6-3",
            "13-7-4",
            "18-10-3",
            "c18103-lifts",
            "34-18-3",
            "quadruple-assembly"
        ],
        "scope": "Universal ordinary C(16,7,5) >= 236, by direct Schoenheim lifting of the universal 103 lower bound at (15,6,4). A consequence of the existing C(14,5,3)>=41 proof, retaining every ceiling. No supplied seed hypothesis, new mechanism or exactness claim."
    },
    '17-8-6': {
        "entry": "CoveringDesigns.C17_8_6",
        "audit_name": "c17-8-6-audit",
        "audit_file": "C17_8_6.lean",
        "principal_theorem": "CoveringDesigns.lower_bound_17_8_6",
        "explicit_theorem": "CoveringDesigns.Audit17_8_6.lower_bound_explicit",
        "summary_path": "results/c17-8-6-verification.json",
        "theorems": [
            "CoveringDesigns.lower_bound_17_8_6"
        ],
        "milestones": [],
        "independent_of": [
            "11-5-2",
            "12-5-2",
            "12-6-3",
            "13-7-4",
            "18-10-3",
            "c18103-lifts",
            "34-18-3",
            "quadruple-assembly"
        ],
        "scope": "Universal ordinary C(17,8,6) >= 502, by direct Schoenheim lifting of the universal 236 lower bound at (16,7,5). A consequence of the existing C(14,5,3)>=41 proof, retaining every ceiling. No supplied seed hypothesis, new mechanism or exactness claim."
    },
    '18-9-7': {
        "entry": "CoveringDesigns.C18_9_7",
        "audit_name": "c18-9-7-audit",
        "audit_file": "C18_9_7.lean",
        "principal_theorem": "CoveringDesigns.lower_bound_18_9_7",
        "explicit_theorem": "CoveringDesigns.Audit18_9_7.lower_bound_explicit",
        "summary_path": "results/c18-9-7-verification.json",
        "theorems": [
            "CoveringDesigns.lower_bound_18_9_7"
        ],
        "milestones": [],
        "independent_of": [
            "11-5-2",
            "12-5-2",
            "12-6-3",
            "13-7-4",
            "18-10-3",
            "c18103-lifts",
            "34-18-3",
            "quadruple-assembly"
        ],
        "scope": "Universal ordinary C(18,9,7) >= 1004, by direct Schoenheim lifting of the universal 502 lower bound at (17,8,6). A consequence of the existing C(14,5,3)>=41 proof, retaining every ceiling. No supplied seed hypothesis, new mechanism or exactness claim."
    },
    '19-10-8': {
        "entry": "CoveringDesigns.C19_10_8",
        "audit_name": "c19-10-8-audit",
        "audit_file": "C19_10_8.lean",
        "principal_theorem": "CoveringDesigns.lower_bound_19_10_8",
        "explicit_theorem": "CoveringDesigns.Audit19_10_8.lower_bound_explicit",
        "summary_path": "results/c19-10-8-verification.json",
        "theorems": [
            "CoveringDesigns.lower_bound_19_10_8"
        ],
        "milestones": [],
        "independent_of": [
            "11-5-2",
            "12-5-2",
            "12-6-3",
            "13-7-4",
            "18-10-3",
            "c18103-lifts",
            "34-18-3",
            "quadruple-assembly"
        ],
        "scope": "Universal ordinary C(19,10,8) >= 1908, by direct Schoenheim lifting of the universal 1004 lower bound at (18,9,7). A consequence of the existing C(14,5,3)>=41 proof, retaining every ceiling. No supplied seed hypothesis, new mechanism or exactness claim."
    },
})
SIX_CONSEQUENCE_PARTS = {
    "C34_18_3": [
        "C34_18_3.LowerBound",
        "C34_18_3.Witness",
        "Foundations.StandardAxioms"
    ],
    "C34_18_3.LowerBound": [
        "TwoKMinusC.OffsetTwo"
    ],
    "C34_18_3.Witness": [
        "Foundations.Relabelling"
    ],
    "C15_6_4": [
        "C15_6_4.LowerBound",
        "Foundations.StandardAxioms"
    ],
    "C15_6_4.LowerBound": [
        "C14_5_3.LowerBound",
        "Schoenheim.LowerBound"
    ],
    "C16_7_5": [
        "C16_7_5.LowerBound",
        "Foundations.StandardAxioms"
    ],
    "C16_7_5.LowerBound": [
        "C15_6_4.LowerBound"
    ],
    "C17_8_6": [
        "C17_8_6.LowerBound",
        "Foundations.StandardAxioms"
    ],
    "C17_8_6.LowerBound": [
        "C16_7_5.LowerBound"
    ],
    "C18_9_7": [
        "C18_9_7.LowerBound",
        "Foundations.StandardAxioms"
    ],
    "C18_9_7.LowerBound": [
        "C17_8_6.LowerBound"
    ],
    "C19_10_8": [
        "C19_10_8.LowerBound",
        "Foundations.StandardAxioms"
    ],
    "C19_10_8.LowerBound": [
        "C18_9_7.LowerBound"
    ]
}

# Five direct lifts of the preserved C(34,18,3) lower theorem.
C34183_LIFTS = ((35, 19, 4, 24, 13), (36, 20, 5, 44, 24),
               (37, 21, 6, 78, 44), (38, 22, 7, 135, 78), (39, 23, 8, 229, 135))
C34183_LIFT_KEYS = tuple(f'{v}-{k}-{t}' for v, k, t, _, _ in C34183_LIFTS)
C34183_LIFT_PARTS = {}
for _v, _k, _t, _bound, _premise in C34183_LIFTS:
    _key = f'{_v}-{_k}-{_t}'
    _suffix = f'{_v}_{_k}_{_t}'
    _module = 'C' + _suffix
    _previous = f'C{_v-1}_{_k-1}_{_t-1}.LowerBound'
    COMPONENTS[_key] = {
        'entry': 'CoveringDesigns.' + _module,
        'audit_name': 'c' + _key + '-audit',
        'audit_file': _module + '.lean',
        'principal_theorem': 'CoveringDesigns.lower_bound_' + _suffix,
        'explicit_theorem': 'CoveringDesigns.Audit' + _suffix + '.lower_bound_explicit',
        'summary_path': 'results/c' + _key + '-verification.json',
        'theorems': ['CoveringDesigns.lower_bound_' + _suffix],
        'milestones': [],
        'independent_of': list(COMPONENTS['34-18-3']['independent_of']),
        'scope': f'Universal ordinary C({_v},{_k},{_t}) >= {_bound}, by direct '
                 f'Schoenheim lifting of the universal {_premise} lower bound at '
                 f'({_v-1},{_k-1},{_t-1}). A consequence of the existing '
                 'C(34,18,3)>=13 theorem, retaining every ceiling. No supplied '
                 'seed hypothesis, attaining-family premise or exactness claim.'
    }
    C34183_LIFT_PARTS[_module] = [_module + '.LowerBound', 'Foundations.StandardAxioms']
    C34183_LIFT_PARTS[_module + '.LowerBound'] = [_previous] + (
        ['Schoenheim.LowerBound'] if _v == 35 else [])


# Reviewed seven-block classification and C(19,9,3); additive, separate components.
SEVEN_C1993_KEYS = ('seven-block-core', 'seven-block', '19-9-3')
COMPONENTS["seven-block-core"] = {
    "entry": "CoveringDesigns.SevenBlock.Core",
    "audit_name": "seven-block-core-audit",
    "audit_file": "SevenBlockCore.lean",
    "principal_theorem": "CoveringDesigns.SevenBlock.classification_ge_two",
    "explicit_theorem": "CoveringDesigns.SevenBlock.classification_ge_two_expanded",
    "summary_path": "results/seven-block-core-verification.json",
    "theorems": [
        "CoveringDesigns.SevenBlock.classification_ge_two",
        "CoveringDesigns.SevenBlock.classification_ge_two_expanded",
        "CoveringDesigns.SevenBlock.support_slack_identity",
        "CoveringDesigns.SevenBlock.support_imbalance_identity",
        "CoveringDesigns.SevenBlock.support_imbalance_nonneg",
        "CoveringDesigns.SevenBlock.partial_overlap_nonneg",
        "CoveringDesigns.SevenBlock.partial_overlap_three",
        "CoveringDesigns.SevenBlock.complete_pair_shadow",
        "CoveringDesigns.SevenBlock.covering_degree_profile",
        "CoveringDesigns.SevenBlock.zero_partial_shadow_divisible",
        "CoveringDesigns.SevenBlock.low_support_fano",
        "CoveringDesigns.SevenBlock.exceptional_support_normal_form",
        "CoveringDesigns.SevenBlock.fano_incidence_identity",
        "CoveringDesigns.SevenBlock.support_fibre_isomorphism",
        "CoveringDesigns.SevenBlock.seven_le_card",
        "CoveringDesigns.SevenBlock.blocks_injective",
        "CoveringDesigns.SevenBlock.template_isCover",
        "CoveringDesigns.SevenBlock.template_injective",
        "CoveringDesigns.SevenBlock.templates_not_isomorphic",
        "CoveringDesigns.SevenBlock.template_attainment",
        "CoveringDesigns.SevenBlock.covering_number_on"
    ],
    "milestones": [
        "CoveringDesigns.SevenBlock.mem_pointSupport",
        "CoveringDesigns.SevenBlock.pointSupport_card",
        "CoveringDesigns.SevenBlock.pointSupport_pair",
        "CoveringDesigns.SevenBlock.pointSupports_meet",
        "CoveringDesigns.SevenBlock.covering_slack",
        "CoveringDesigns.SevenBlock.line_card",
        "CoveringDesigns.SevenBlock.line_meet",
        "CoveringDesigns.SevenBlock.line_inter_card",
        "CoveringDesigns.SevenBlock.line_injective",
        "CoveringDesigns.SevenBlock.pair_unique_line",
        "CoveringDesigns.SevenBlock.position_degree",
        "CoveringDesigns.SevenBlock.high_card",
        "CoveringDesigns.SevenBlock.high_line_meet",
        "CoveringDesigns.SevenBlock.high_high_meet",
        "CoveringDesigns.SevenBlock.exceptional_codegree",
        "CoveringDesigns.SevenBlock.fano_weights_unique",
        "CoveringDesigns.SevenBlock.IndexedIsomorphic.refl",
        "CoveringDesigns.SevenBlock.IndexedIsomorphic.symm",
        "CoveringDesigns.SevenBlock.IndexedIsomorphic.trans",
        "CoveringDesigns.SevenBlock.incidence_degree_eq",
        "CoveringDesigns.SevenBlock.incidence_codegree_eq",
        "CoveringDesigns.SevenBlock.degree_floor",
        "CoveringDesigns.SevenBlock.ordinary_seven_le_card",
        "CoveringDesigns.SevenBlock.indexed_ordinary_equivalence",
        "CoveringDesigns.SevenBlock.ordinary_isomorphism_to_indexed",
        "CoveringDesigns.SevenBlock.fano_partial_overlap_zero",
        "CoveringDesigns.SevenBlock.exceptional_codegree_dichotomy",
        "CoveringDesigns.SevenBlock.low_support_shadow",
        "CoveringDesigns.SevenBlock.fibre_weight_sum",
        "CoveringDesigns.SevenBlock.fibre_weight_row",
        "CoveringDesigns.SevenBlock.shadow_positive",
        "CoveringDesigns.SevenBlock.consecutive_nonneg",
        "CoveringDesigns.SevenBlock.imbalance_identity",
        "CoveringDesigns.SevenBlock.imbalance_nonneg",
        "CoveringDesigns.SevenBlock.support_excess_eq",
        "CoveringDesigns.SevenBlock.support_moment_eq",
        "CoveringDesigns.SevenBlock.mem_templateBlock",
        "CoveringDesigns.SevenBlock.template_point_card",
        "CoveringDesigns.SevenBlock.template_uniform",
        "CoveringDesigns.SevenBlock.template_supports_meet",
        "CoveringDesigns.SevenBlock.template_covers",
        "CoveringDesigns.SevenBlock.template_degree",
        "CoveringDesigns.SevenBlock.template_degree_four_iff",
        "CoveringDesigns.SevenBlock.template_line_fibre_card",
        "CoveringDesigns.SevenBlock.template_exceptional_codegree",
        "CoveringDesigns.SevenBlock.template_family_isCover",
        "CoveringDesigns.SevenBlock.template_family_card"
    ],
    "independent_of": [
        "11-5-2",
        "12-5-2",
        "12-6-3",
        "13-7-4",
        "19-9-3"
    ],
    "scope": "Universal a>=2 classification of indexed seven-block (7a+4,3a+2,2) coverings into two actual weighted Fano forms; signed support slack, complete pair shadow, boundary recovery, multiplicities and exceptional supports. Both constructions and the known numerical family for every a>=1. Independent of the Stanton adapter."
}
COMPONENTS["seven-block"] = {
    "entry": "CoveringDesigns.SevenBlock",
    "audit_name": "seven-block-audit",
    "audit_file": "SevenBlock.lean",
    "principal_theorem": "CoveringDesigns.SevenBlock.classification",
    "explicit_theorem": "CoveringDesigns.SevenBlock.classification_expanded",
    "summary_path": "results/seven-block-verification.json",
    "theorems": [
        "CoveringDesigns.SevenBlock.classification_one",
        "CoveringDesigns.SevenBlock.classification",
        "CoveringDesigns.SevenBlock.classification_expanded"
    ],
    "milestones": [],
    "independent_of": [
        "12-5-2",
        "12-6-3",
        "13-7-4",
        "19-9-3"
    ],
    "scope": "All-a>=1 unique-form classification by actual point and occurrence equivalences, using the unchanged ordinary Stanton classification only for a=1 and a proved ordinary/indexed adapter. Equal point supports are retained; repeated block images are excluded internally."
}
COMPONENTS["19-9-3"] = {
    "entry": "CoveringDesigns.C19_9_3",
    "audit_name": "c19-9-3-audit",
    "audit_file": "C19_9_3.lean",
    "principal_theorem": "CoveringDesigns.covering_number_19_9_3",
    "explicit_theorem": "CoveringDesigns.covering_number_19_9_3_expanded_on",
    "summary_path": "results/c19-9-3-verification.json",
    # Retained results are compiled and audited without entering the new lower bound.
    "verification_entries": [
        "CoveringDesigns.C19_9_3.TwoSingleExclusion",
        "CoveringDesigns.C19_9_3.FourSingleExclusion"
    ],
    "theorems": [
        "CoveringDesigns.C19_9_3.seventeen_le_card",
        "CoveringDesigns.C19_9_3.seventeen_le_card_expanded",
        "CoveringDesigns.lower_bound_19_9_3_on",
        "CoveringDesigns.lower_bound_19_9_3",
        "CoveringDesigns.lower_bound_19_9_3_expanded",
        "CoveringDesigns.covering_number_19_9_3_on",
        "CoveringDesigns.covering_number_19_9_3",
        "CoveringDesigns.covering_number_19_9_3_expanded_on",
        "CoveringDesigns.knownCover17_19_9_3_isCover",
        "CoveringDesigns.knownCover17_19_9_3_on_isCover",
        "CoveringDesigns.knownCover17_19_9_3_card",
        "CoveringDesigns.knownCover17_19_9_3_on_card",
        "CoveringDesigns.C19_9_3.literal_link_trace",
        "CoveringDesigns.C19_9_3.literal_link_pair_trace",
        "CoveringDesigns.C19_9_3.complementary_agreement_identity",
        "CoveringDesigns.C19_9_3.actual_affine_configuration",
        "CoveringDesigns.C19_9_3.column_forms",
        "CoveringDesigns.C19_9_3.actual_column_forms",
        "CoveringDesigns.C19_9_3.actual_weak_completion",
        "CoveringDesigns.C19_9_3.weak_completion_impossible",
        "CoveringDesigns.C19_9_3.character_orthogonal",
        "CoveringDesigns.C19_9_3.coefficient_extraction",
        "CoveringDesigns.C19_9_3.character_parseval",
        "CoveringDesigns.C19_9_3.character_unit_square",
        "CoveringDesigns.IndexedPadding.pad",
        "CoveringDesigns.IndexedPadding.lower_of_fixed_exclusion"
    ],
    "milestones": [
        "CoveringDesigns.C19_9_3.minimum_root_fano",
        "CoveringDesigns.C19_9_3.minimum_trace_four",
        "CoveringDesigns.C19_9_3.minimum_subset_multiplicity",
        "CoveringDesigns.C19_9_3.minimum_traces_intersection",
        "CoveringDesigns.C19_9_3.affine_nonminimum_row",
        "CoveringDesigns.C19_9_3.empty_nonminimum_row",
        "CoveringDesigns.C19_9_3.affine_plane_card",
        "CoveringDesigns.C19_9_3.affine_point_degree",
        "CoveringDesigns.C19_9_3.affine_pair_degree",
        "CoveringDesigns.C19_9_3.affine_triple_degree",
        "CoveringDesigns.C19_9_3.affine_root_line",
        "CoveringDesigns.C19_9_3.affine_root_all_lines",
        "CoveringDesigns.C19_9_3.column_character_identity",
        "CoveringDesigns.C19_9_3.column_incidence_sum",
        "CoveringDesigns.C19_9_3.minimum_exceptional_trace",
        "CoveringDesigns.C19_9_3.minimum_contained_trace_companion",
        "CoveringDesigns.C19_9_3.no_minimum_triple_three",
        "CoveringDesigns.C19_9_3.sixteen_le_card",
        "CoveringDesigns.C19_9_3.ordinary_sixteen_le_card",
        "CoveringDesigns.C19_9_3.no_fifteen",
        "CoveringDesigns.C19_9_3.sixteen_blocks_injective",
        "CoveringDesigns.C19_9_3.pair_floor",
        "CoveringDesigns.C19_9_3.degree_floor",
        "CoveringDesigns.C19_9_3.mem_minimumPoints",
        "CoveringDesigns.C19_9_3.minimum_count_bound",
        "CoveringDesigns.C19_9_3.eight_minimum_points",
        "CoveringDesigns.C19_9_3.degree_excess",
        "CoveringDesigns.C19_9_3.pair_sum",
        "CoveringDesigns.C19_9_3.minimum_incidence_coordinates",
        "CoveringDesigns.C19_9_3.minimum_ordinary_trace",
        "CoveringDesigns.C19_9_3.minimum_two_trace_exceptional",
        "CoveringDesigns.C19_9_3.minimum_two_trace_agreement",
        "CoveringDesigns.C19_9_3.no_three_minimum_exceptions",
        "CoveringDesigns.C19_9_3.minimum_ordinary_pair_profile",
        "CoveringDesigns.C19_9_3.no_sixteen",
        "CoveringDesigns.C19_9_3.minimum_link_classification",
        "CoveringDesigns.C19_9_3.actual_link_degree",
        "CoveringDesigns.C19_9_3.actual_link_codegree",
        "CoveringDesigns.C19_9_3.minimum_profile",
        "CoveringDesigns.C19_9_3.minimum_pair_le_four",
        "CoveringDesigns.C19_9_3.minimum_pair_ordinary",
        "CoveringDesigns.C19_9_3.minimum_points_card",
        "CoveringDesigns.C19_9_3.nonminimum_degree",
        "CoveringDesigns.C19_9_3.minimum_triple_one",
        "CoveringDesigns.C19_9_3.character_sign",
        "CoveringDesigns.C19_9_3.character_balanced",
        "CoveringDesigns.C19_9_3.coefficients_zero",
        "CoveringDesigns.C19_9_3.three_support_count",
        "CoveringDesigns.C19_9_3.pointSupport_triple",
        "CoveringDesigns.C19_9_3.three_ordinary_roots_no_fourth",
        "CoveringDesigns.C19_9_3.no_three_ordinary_minima",
        "CoveringDesigns.knownBlocks17_19_9_3_distinct",
        "CoveringDesigns.knownBlocks17_19_9_3_length",
        "CoveringDesigns.knownCover17_19_9_3_mem",
        "CoveringDesigns.triple_count_19_9_3",
        "CoveringDesigns.knownCover17_19_9_3_uniform",
        "CoveringDesigns.knownCover17_19_9_3_covers",
        "CoveringDesigns.upper_bound_19_9_3",
        "CoveringDesigns.upper_bound_19_9_3_on",
        "CoveringDesigns.IndexedPadding.nonempty_occurrences"
    ],
    "independent_of": [
        "11-5-2",
        "12-5-2",
        "12-6-3",
        "13-7-4",
        "18-10-3",
        "20-11-3"
    ],
    "scope": "Unconditional indexed lower seventeen and ordinary C(19,9,3)=17 on arbitrary labels and Fin 19. Actual-link agreement, affine recognition, column forms and all budgets are derived internally; nonempty padding handles smaller budgets. Historical Rade Belic witness is kernel checked, with separate retained-data transcription checks. No Stanton, GPPT, C18, C20 or C26 result dependency."
}

# Exact direct project imports; no research or proof-search input is allowed.
SEVEN_C1993_IMPORTS = {
    "CoveringDesigns.C19_9_3.ActualAffine": [
        "CoveringDesigns.C19_9_3.MinimumPoints",
        "CoveringDesigns.C19_9_3.AffineModel"
    ],
    "CoveringDesigns.C19_9_3.ActualColumns": [
        "CoveringDesigns.C19_9_3.ActualAffine",
        "CoveringDesigns.C19_9_3.ColumnForms"
    ],
    "CoveringDesigns.C19_9_3.AffineModel": [
        "CoveringDesigns.C19_9_3.Orthogonality",
        "CoveringDesigns.Equality.FiniteSum"
    ],
    "CoveringDesigns.C19_9_3.BudgetTools": [
        "CoveringDesigns.C19_9_3.FanoBudgets"
    ],
    "CoveringDesigns.C19_9_3.ColumnForms": [
        "CoveringDesigns.C19_9_3.AffineModel"
    ],
    "CoveringDesigns.C19_9_3.ColumnWeights": [
        "CoveringDesigns.C19_9_3.Completion"
    ],
    "CoveringDesigns.C19_9_3.Completion": [
        "CoveringDesigns.C19_9_3.ActualColumns",
        "CoveringDesigns.C19_9_3.Fifteen"
    ],
    "CoveringDesigns.C19_9_3.CoveringNumber": [
        "CoveringDesigns.C19_9_3.LowerBound",
        "CoveringDesigns.C19_9_3.Witness"
    ],
    "CoveringDesigns.C19_9_3.ExcessRoots": [
        "CoveringDesigns.C19_9_3.ThreeRoots"
    ],
    "CoveringDesigns.C19_9_3.FanoBudgets": [
        "CoveringDesigns.C19_9_3.ColumnWeights"
    ],
    "CoveringDesigns.C19_9_3.Fifteen": [
        "CoveringDesigns.C19_9_3.Incidence",
        "CoveringDesigns.MulticoverIncidence.LowerBound",
        "CoveringDesigns.Multicover.Family"
    ],
    "CoveringDesigns.C19_9_3.FourSingleExclusion": [
        "CoveringDesigns.C19_9_3.BudgetTools"
    ],
    "CoveringDesigns.C19_9_3.Incidence": [
        "CoveringDesigns.Multicover.Schoenheim",
        "CoveringDesigns.LabelledCliques.Extensions",
        "CoveringDesigns.Foundations.StandardAxioms"
    ],
    "CoveringDesigns.C19_9_3.LinkTraceRules": [
        "CoveringDesigns.C19_9_3.MinimumLinks",
        "CoveringDesigns.C19_9_3.TraceAgreement"
    ],
    "CoveringDesigns.C19_9_3.LowerBound": [
        "CoveringDesigns.C19_9_3.ShortCompletion",
        "CoveringDesigns.Foundations.IndexedPadding"
    ],
    "CoveringDesigns.C19_9_3.WeakCompletion": [
        "CoveringDesigns.C19_9_3.ActualColumns"
    ],
    "CoveringDesigns.C19_9_3.ShortCompletion": [
        "CoveringDesigns.C19_9_3.WeakCompletion"
    ],
    "CoveringDesigns.C19_9_3.MinimumLinks": [
        "CoveringDesigns.C19_9_3.Incidence",
        "CoveringDesigns.SevenBlock.Core"
    ],
    "CoveringDesigns.C19_9_3.MinimumPoints": [
        "CoveringDesigns.C19_9_3.ExcessRoots"
    ],
    "CoveringDesigns.C19_9_3.Orthogonality": [
        "CoveringDesigns.SevenBlock.Fano"
    ],
    "CoveringDesigns.C19_9_3.RootPartition": [
        "CoveringDesigns.C19_9_3.LinkTraceRules"
    ],
    "CoveringDesigns.C19_9_3.ThreeRoots": [
        "CoveringDesigns.C19_9_3.RootPartition"
    ],
    "CoveringDesigns.C19_9_3.TraceAgreement": [
        "CoveringDesigns.SevenBlock.Degrees"
    ],
    "CoveringDesigns.C19_9_3.TwoSingleExclusion": [
        "CoveringDesigns.C19_9_3.BudgetTools"
    ],
    "CoveringDesigns.C19_9_3.Witness": [
        "CoveringDesigns.Foundations.Relabelling",
        "CoveringDesigns.Foundations.StandardAxioms"
    ],
    "CoveringDesigns.C19_9_3": [
        "CoveringDesigns.C19_9_3.CoveringNumber"
    ],
    "CoveringDesigns.Foundations.IndexedPadding": [
        "CoveringDesigns.Multicover.Basic",
        "CoveringDesigns.Foundations.StandardAxioms"
    ],
    "CoveringDesigns.SevenBlock.Classification": [
        "CoveringDesigns.SevenBlock.LowFano",
        "CoveringDesigns.SevenBlock.SupportFibres",
        "CoveringDesigns.SevenBlock.FanoSymmetry",
        "CoveringDesigns.SevenBlock.Templates"
    ],
    "CoveringDesigns.SevenBlock.Core": [
        "CoveringDesigns.SevenBlock.Classification"
    ],
    "CoveringDesigns.SevenBlock.Degrees": [
        "CoveringDesigns.SevenBlock.Indexed",
        "CoveringDesigns.SevenBlock.SupportSlack",
        "CoveringDesigns.Equality.FiniteSum"
    ],
    "CoveringDesigns.SevenBlock.Fano": [
        "CoveringDesigns.Foundations.Basic",
        "CoveringDesigns.Foundations.StandardAxioms"
    ],
    "CoveringDesigns.SevenBlock.FanoSymmetry": [
        "CoveringDesigns.SevenBlock.Fano",
        "CoveringDesigns.Foundations.Relabelling"
    ],
    "CoveringDesigns.SevenBlock.Indexed": [
        "CoveringDesigns.Multicover.Family",
        "CoveringDesigns.Foundations.Relabelling",
        "CoveringDesigns.Foundations.StandardAxioms"
    ],
    "CoveringDesigns.SevenBlock.LowFano": [
        "CoveringDesigns.SevenBlock.LowShadow",
        "CoveringDesigns.SevenBlock.ShadowGeometry"
    ],
    "CoveringDesigns.SevenBlock.LowShadow": [
        "CoveringDesigns.SevenBlock.Degrees",
        "CoveringDesigns.SevenBlock.SupportShadow"
    ],
    "CoveringDesigns.SevenBlock.ShadowGeometry": [
        "CoveringDesigns.SevenBlock.Fano",
        "CoveringDesigns.Foundations.Relabelling"
    ],
    "CoveringDesigns.SevenBlock.Stanton": [
        "CoveringDesigns.SevenBlock.Templates",
        "CoveringDesigns.C11_5_2.Classification"
    ],
    "CoveringDesigns.SevenBlock.SupportFibres": [
        "CoveringDesigns.SevenBlock.Degrees",
        "CoveringDesigns.SevenBlock.Fano"
    ],
    "CoveringDesigns.SevenBlock.SupportShadow": [
        "CoveringDesigns.SevenBlock.SupportSlack"
    ],
    "CoveringDesigns.SevenBlock.SupportSlack": [
        "CoveringDesigns.Foundations.Intersecting",
        "CoveringDesigns.Foundations.StandardAxioms"
    ],
    "CoveringDesigns.SevenBlock.Templates": [
        "CoveringDesigns.SevenBlock.Indexed",
        "CoveringDesigns.SevenBlock.Fano"
    ],
    "CoveringDesigns.SevenBlock": [
        "CoveringDesigns.SevenBlock.Core",
        "CoveringDesigns.SevenBlock.Stanton"
    ]
}


def source(module):
    return ROOT / (module.replace('.', '/') + '.lean')


def project_imports(text, filename='<source>'):
    """Read local dependencies from Lean's header, without compiling the file.

    Follows Lean 4.34.1 Parser/Module/Syntax.lean and Parser/Basic.lean:
    optional module/prelude, then (public? meta? import all? ident)*.
    Ordinary comments are whitespace; doc comments begin the body. Only the
    header is scanned, so body strings, quotations and documentation cannot
    invent dependencies. This is not a validator for Lean's command language.

    Escaped name segments are decoded. Path separators, literal dots and
    empty/control/space segments are rejected, even on external imports:
    those spellings can alias audited files while evading namespace checks.
    """
    pos, imports = 0, []

    def error(reason):
        line = text.count('\n', 0, pos) + 1
        raise ValueError(f'Cannot audit Lean imports in {filename}:{line}: {reason}')

    def whitespace():
        nonlocal pos
        while pos < len(text):
            if text[pos] in ' \t\r\n':
                pos += 1
            elif text.startswith('--', pos):
                end = text.find('\n', pos + 2)
                pos = len(text) if end < 0 else end + 1
            elif text.startswith('/-', pos) and not text.startswith(('/--', '/-!'), pos):
                pos += 2
                depth = 1
                while depth:
                    if pos == len(text):
                        error('unterminated block comment')
                    if text.startswith('/-', pos):
                        depth += 1
                        pos += 2
                    elif text.startswith('-/', pos):
                        depth -= 1
                        pos += 2
                    else:
                        pos += 1
            else:
                break

    def keyword(word):
        nonlocal pos
        whitespace()
        match = _IMPORT_ID.match(text, pos)
        if match is None or match.group() != word:
            return False
        end = match.end()
        # A dotted name such as module.Foo is one identifier, not a keyword.
        if text[end:end + 1] == '.' and (text[end + 1:end + 2] == '«' or
                                       _IMPORT_ID.match(text, end + 1)):
            return False
        pos = end
        return True

    def module_name():
        nonlocal pos
        whitespace()
        parts = []
        while True:
            if text[pos:pos + 1] == '«':
                end = text.find('»', pos + 1)
                if end < 0:
                    error('unterminated escaped identifier')
                part = text[pos + 1:end]
                pos = end + 1
            else:
                match = _IMPORT_ID.match(text, pos)
                if match is None:
                    error('expected module identifier')
                part = match.group()
                pos = match.end()
            if not part or any(c in './\\' or c.isspace() or ord(c) < 32 for c in part):
                error('noncanonical module name; use ordinary dotted name segments')
            parts.append(part)
            if text[pos:pos + 1] != '.':
                break
            pos += 1
        root = parts[0]
        if root not in _LOCAL_IMPORT_ROOTS and root.casefold() in {
                name.casefold() for name in _LOCAL_IMPORT_ROOTS}:
            error('noncanonical project namespace casing')
        return parts

    is_module = keyword('module')
    keyword('prelude')
    while True:
        public = keyword('public')
        meta = keyword('meta')
        if not keyword('import'):
            return imports
        all_data = keyword('all')
        if (public or meta or all_data) and not is_module:
            error('import modifiers require a module header')
        if public and all_data:
            error('public import all is not a valid Lean import')
        parts = module_name()
        if parts[0] in _LOCAL_IMPORT_ROOTS:
            imports.append('.'.join(parts))
        elif any(path.exists() for path in (
                ROOT / parts[0], ROOT / (parts[0] + '.lean'),
                ROOT / '.lake/build/lib/lean' / parts[0],
                ROOT / '.lake/build/lib/lean' / (parts[0] + '.olean'))):
            error('project-local imports must use CoveringDesigns or Explorations')


class SourceGraph:
    """One source-check operation's parsed imports and transitive closures.

    Never retain this object across operations: a fresh check/plan must inspect
    current source files, canonical paths and local import shadowing again.
    These caches contain source dependencies only, never proof/audit outcomes.
    """

    def __init__(self):
        self._imports = {}
        self._closures = {}
        self._directory_names = {}
        self._canonical_paths = set()

    def imports(self, module):
        if module not in self._imports:
            path = source(module)
            assert path.is_file(), f'Missing local import: {path}'
            # Check each path segment, retaining exact spelling and symlink
            # rejection even on case-insensitive filesystems.
            parent = ROOT
            for part in path.relative_to(ROOT).parts:
                child = parent / part
                if child not in self._canonical_paths:
                    if parent not in self._directory_names:
                        self._directory_names[parent] = {entry.name for entry in parent.iterdir()}
                    if part not in self._directory_names[parent] or child.is_symlink():
                        raise ValueError(f'Cannot audit Lean imports in {path}: noncanonical local path')
                    self._canonical_paths.add(child)
                parent = child
            self._imports[module] = tuple(project_imports(path.read_text(), path))
        return self._imports[module]

    def module_order(self, entries):
        """Stable topological order, with a fresh cycle/visited set per walk."""
        ordered, seen, active = [], set(), set()

        def visit(module):
            if module in seen:
                return
            assert module not in active, f'Import cycle at {module}'
            active.add(module)
            for dependency in self.imports(module):
                visit(dependency)
            active.remove(module)
            seen.add(module)
            ordered.append(module)

        for entry in entries:
            visit(entry)
        return ordered

    def closure(self, entry):
        active = set()

        def visit(module):
            if module in self._closures:
                return self._closures[module]
            assert module not in active, f'Import cycle at {module}'
            active.add(module)
            paths = {source(module)}
            for dependency in self.imports(module):
                paths.update(visit(dependency))
            active.remove(module)
            self._closures[module] = frozenset(paths)
            return self._closures[module]

        # Callers build allowed sets with |= and add; never expose cached sets.
        return set(visit(entry))


def module_order(entries):
    """Topological order of current project imports; external dependencies are installed."""
    return SourceGraph().module_order(entries)


def closure(entry):
    return SourceGraph().closure(entry)


PUBLICATION_BOUNDARIES = {'caro-tuza': 'CoveringDesigns.CaroTuza', 'horsley': 'CoveringDesigns.Horsley', 'schoenheim': 'CoveringDesigns.Schoenheim', '11-5-2': 'CoveringDesigns.C11_5_2', '12-5-2': 'CoveringDesigns.C12_5_2', '12-6-3': 'CoveringDesigns.C12_6_3', '13-7-4': 'CoveringDesigns.C13_7_4', 'horsley-lifts': 'CoveringDesigns.Applications.HorsleyLifts', 'horsley-singh': 'CoveringDesigns.HorsleySingh', 'equality': 'CoveringDesigns.Equality', '17-9-5': 'CoveringDesigns.C17_9_5', 'higher-incidence': 'CoveringDesigns.HigherIncidence', 'weighted': 'CoveringDesigns.Weighted', '47-14-5': 'CoveringDesigns.C47_14_5', '42-15-5': 'CoveringDesigns.C42_15_5', 'large-defect': 'CoveringDesigns.LargeDefect', 'small-defect': 'CoveringDesigns.SmallDefect', 'small-defect-b': 'CoveringDesigns.SmallDefectB', 'small-defect-c': 'CoveringDesigns.SmallDefectC', 'multicover': 'CoveringDesigns.Multicover', 'multicover-incidence': 'CoveringDesigns.MulticoverIncidence', 'multicover-large-defect': 'CoveringDesigns.MulticoverLargeDefect', 'coefficient-positivity': 'CoveringDesigns.CoefficientPositivity', 'affine-constructions': 'CoveringDesigns.AffineConstructions', 'affine-schoenheim': 'CoveringDesigns.AffineSchoenheim', 'affine-optimality': 'CoveringDesigns.AffineOptimality', 'lifting-comparison': 'CoveringDesigns.LiftingComparison', 'schoenheim-improvement': 'CoveringDesigns.SchoenheimImprovement', 'multicover-small-defect': 'CoveringDesigns.MulticoverSmallDefect', 'low-degree-selection': 'CoveringDesigns.LowDegreeSelection', 'seed-comparison': 'CoveringDesigns.SeedComparison', 'exact-design': 'CoveringDesigns.ExactDesign', 'point-reduction': 'CoveringDesigns.PointReduction', 'base-affine': 'CoveringDesigns.BaseAffine', 'schoenheim-family-comparison': 'CoveringDesigns.SchoenheimFamilyComparison', 'max-degree-sequence': 'CoveringDesigns.MaxDegreeSequence', 'max-guarantee': 'CoveringDesigns.MaxGuarantee', 'max-covering': 'CoveringDesigns.MaxCovering', 'max-higher-covering': 'CoveringDesigns.MaxHigherCovering', '14-8-5': 'CoveringDesigns.C14_8_5', '59-17-5': 'CoveringDesigns.C59_17_5', '66-18-5': 'CoveringDesigns.C66_18_5', '79-22-5': 'CoveringDesigns.C79_22_5', '87-23-5': 'CoveringDesigns.C87_23_5', '98-22-5': 'CoveringDesigns.C98_22_5', 'labelled-cliques': 'CoveringDesigns.LabelledCliques', 'turan-duality': 'CoveringDesigns.Turan.Duality', 'turan': 'CoveringDesigns.Turan', 'de-caen': 'CoveringDesigns.DeCaen', 'chvatal': 'CoveringDesigns.Chvatal', 'gkp-combination': 'CoveringDesigns.GKPCombination', 'gkp-induced': 'CoveringDesigns.GKPInduced', 'gkp-induced-averaging': 'CoveringDesigns.GKPInducedAveraging', 'projective-hyperplanes': 'CoveringDesigns.ProjectiveHyperplanes', 'finite-flat-geometry': 'CoveringDesigns.FiniteGeometry', 'degree-selected': 'CoveringDesigns.DegreeSelected', '20-11-3': 'CoveringDesigns.C20_11_3', 'two-k-minus-two': 'CoveringDesigns.TwoKMinusTwo', 'two-k-minus-two-equality': 'CoveringDesigns.TwoKMinusTwoEquality', 'two-k-minus-c': 'CoveringDesigns.TwoKMinusC', 'two-k-minus-c-general': 'CoveringDesigns.TwoKMinusCGeneral', 'two-k-minus-two-tightening': 'CoveringDesigns.TwoKMinusTwoTightening', 'rank-slack-capacity': 'CoveringDesigns.RankSlackCapacity', 'saturated-matching': 'CoveringDesigns.SaturatedMatching', '18-10-3': 'CoveringDesigns.C18_10_3.SquareSupport', 'c18103-lifts': 'CoveringDesigns.Applications.C18103Lifts', '14-5-3': 'CoveringDesigns.C14_5_3.Examples', 'quadruple-assembly': 'CoveringDesigns.QuadrupleAssembly', '34-18-3': 'CoveringDesigns.C34_18_3', '15-6-4': 'CoveringDesigns.C15_6_4', '16-7-5': 'CoveringDesigns.C16_7_5', '17-8-6': 'CoveringDesigns.C17_8_6', '18-9-7': 'CoveringDesigns.C18_9_7', '19-10-8': 'CoveringDesigns.C19_10_8', '35-19-4': 'CoveringDesigns.C35_19_4', '36-20-5': 'CoveringDesigns.C36_20_5', '37-21-6': 'CoveringDesigns.C37_21_6', '38-22-7': 'CoveringDesigns.C38_22_7', '39-23-8': 'CoveringDesigns.C39_23_8', 'seven-block-core': 'CoveringDesigns.SevenBlock.Core', 'seven-block': 'CoveringDesigns.SevenBlock', '19-9-3': 'CoveringDesigns.C19_9_3'}

def check_sources():
    publication_boundaries = PUBLICATION_BOUNDARIES
    closure = SourceGraph().closure
    closures = {key: closure(item['entry']) for key, item in COMPONENTS.items()}
    # The new branches consume earlier interfaces without changing their owners.
    new_sources = {source(module) for module in SEVEN_C1993_IMPORTS}
    for key, paths in closures.items():
        if key not in SEVEN_C1993_KEYS:
            assert not paths & new_sources, f'Established component {key} imports seven-block/C19 additions'
    for module, dependencies in SEVEN_C1993_IMPORTS.items():
        actual = project_imports(source(module).read_text(), str(source(module)))
        assert actual == dependencies, f'Seven-block/C19 direct interface changed: {module}'
    for key in ('seven-block-core', '19-9-3'):
        assert not any('C11_5_2' in p.parts or p.name == 'C11_5_2.lean' or
                       p == source('CoveringDesigns.SevenBlock.Stanton') or
                       p == source('CoveringDesigns.SevenBlock') for p in closures[key]), \
            f'{key} acquired the small-case adapter'
    fifteen = closure('CoveringDesigns.C19_9_3.Fifteen')
    assert not any('SevenBlock' in p.parts or p.name == 'SevenBlock.lean' for p in fifteen), \
        'Independent fifteen exclusion depends on classification'
    assert source('CoveringDesigns.C19_9_3.LowerBound') not in fifteen, \
        'Independent fifteen exclusion depends on the final exclusion'
    assert COMPONENTS['19-9-3'].get('verification_entries') == [
        'CoveringDesigns.C19_9_3.TwoSingleExclusion',
        'CoveringDesigns.C19_9_3.FourSingleExclusion'], \
        'Retained C19 completion results must still be freshly compiled for their audit'
    parent = closures['19-9-3']
    assert not any('MulticoverIncidence' in p.parts or 'Incidence' in p.parts or
                   p.name in ('Fifteen.lean', 'Completion.lean', 'ColumnWeights.lean',
                              'FanoBudgets.lean', 'BudgetTools.lean',
                              'TwoSingleExclusion.lean', 'FourSingleExclusion.lean')
                   for p in parent), 'Short C19 completion acquired the old rank/completion branch'
    # Existing components cannot acquire a dependency on the five new lifts.
    lift_sources = {source('CoveringDesigns.' + part) for part in C34183_LIFT_PARTS}
    for key, paths in closures.items():
        if key not in C34183_LIFT_KEYS:
            assert not paths & lift_sources, f'Established component {key} imports a C34 lift'
    for part, dependencies in C34183_LIFT_PARTS.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'C34 lift {part} imports outside its declared interface'
    # The six numerical consequences reuse only their declared earlier inputs.
    # Only the five authorised C34 lifts additionally consume the lower seed.
    consequence_sources = {source('CoveringDesigns.' + part) for part in SIX_CONSEQUENCE_PARTS}
    for key, paths in closures.items():
        if key not in ('34-18-3', *C1453_LIFT_KEYS, *C34183_LIFT_KEYS):
            assert not paths & consequence_sources, f'Established component {key} imports a six-consequence module'
    for part, dependencies in SIX_CONSEQUENCE_PARTS.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'Six-consequence {part} imports outside its declared interface'
    # Earlier components cannot acquire the new seed/data construction.
    quad_entry = 'CoveringDesigns.QuadrupleAssembly'
    quad_sources = {p for p in closures['quadruple-assembly']
                    if p == source(quad_entry) or 'QuadrupleAssembly' in p.parts}
    for key, paths in closures.items():
        if key != 'quadruple-assembly':
            assert not paths & quad_sources, f'Established component {key} imports quadruple assembly'
    for module in ('Budget', 'Distinctness', 'Coverage', 'ProductSubstitution'):
        assert not any('SeedData' in p.parts or 'WitnessData' in p.parts or p.stem == 'SeedInstances'
                       for p in closure(quad_entry + '.' + module)), 'General assembly depends on instances'
    assert not any('WitnessData' in p.parts for p in closure(quad_entry + '.SeedInstances')), 'Seed chain depends on final files'
    # Exact C14 dependency graph: no old component may acquire these modules.
    c1453_parts = {'CoveringDesigns.C14_5_3.AlmostExactCounts': ['CoveringDesigns.C14_5_3.Incidence'],
     'CoveringDesigns.C14_5_3.AlmostExactIntersections': ['CoveringDesigns.C14_5_3.AlmostExactTraces',
                                                          'CoveringDesigns.C14_5_3.ExactLink'],
     'CoveringDesigns.C14_5_3.AlmostExactLink': ['CoveringDesigns.C14_5_3.AlmostExactIntersections'],
     'CoveringDesigns.C14_5_3.AlmostExactTraces': ['CoveringDesigns.C14_5_3.AlmostExactCounts'],
     'CoveringDesigns.C14_5_3.Completion': ['CoveringDesigns.C14_5_3.ExactLink'],
     'CoveringDesigns.C14_5_3.Completion28': ['CoveringDesigns.C14_5_3.LowerBound'],
     'CoveringDesigns.C14_5_3.CompletionCharges': ['CoveringDesigns.C14_5_3.Completion'],
     'CoveringDesigns.C14_5_3.ExactLink': ['CoveringDesigns.C14_5_3.Incidence'],
     'CoveringDesigns.C14_5_3.Examples': ['CoveringDesigns.C14_5_3'],
     'CoveringDesigns.C14_5_3.Forty': ['CoveringDesigns.C14_5_3.Completion'],
     'CoveringDesigns.C14_5_3.FourMinimum': ['CoveringDesigns.C14_5_3.MinimumCompatibility'],
     'CoveringDesigns.C14_5_3.Incidence': ['CoveringDesigns.ExactDesign.Counting',
                                           'CoveringDesigns.LabelledCliques.Extensions'],
     'CoveringDesigns.C14_5_3.LowerBound': ['CoveringDesigns.C14_5_3.ParentCharges',
                                            'CoveringDesigns.C14_5_3.FourMinimum',
                                            'CoveringDesigns.Multicover.Family'],
     'CoveringDesigns.C14_5_3.MinimumCompatibility': ['CoveringDesigns.C14_5_3.MinimumTraces'],
     'CoveringDesigns.C14_5_3.MinimumTraces': ['CoveringDesigns.C14_5_3.SpecialBlocks'],
     'CoveringDesigns.C14_5_3.ParentCharges': ['CoveringDesigns.C14_5_3.SpecialBlocks',
                                               'CoveringDesigns.C14_5_3.CompletionCharges'],
     'CoveringDesigns.C14_5_3.ParentLinks': ['CoveringDesigns.C14_5_3.Forty',
                                             'CoveringDesigns.C14_5_3.AlmostExactLink'],
     'CoveringDesigns.C14_5_3.SpecialBlocks': ['CoveringDesigns.C14_5_3.ParentLinks'],
     'CoveringDesigns.C14_5_3.Witness': ['CoveringDesigns.Foundations.Relabelling'],
     'CoveringDesigns.C14_5_3': ['CoveringDesigns.C14_5_3.LowerBound',
                                 'CoveringDesigns.C14_5_3.Completion28',
                                 'CoveringDesigns.C14_5_3.Witness',
                                 'CoveringDesigns.Foundations.StandardAxioms']}
    c1453_sources = {source(module) for module in c1453_parts}
    for key, paths in closures.items():
        if key not in ('14-5-3', *C1453_LIFT_KEYS):
            assert not paths & c1453_sources, f'Established component {key} imports C14_5_3'
    for module, dependencies in c1453_parts.items():
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure(dependency)
        assert closure(module) == expected, f'C14 interface imports changed: {module}'
    c1453_lower = closure('CoveringDesigns.C14_5_3.LowerBound')
    for part in ('Completion28', 'Witness', 'Examples'):
        assert source('CoveringDesigns.C14_5_3.' + part) not in c1453_lower, \
            f'C14 lower bound depends on a downstream or unrelated stage: {part}'
    for stage, forbidden in (('Completion', 'Forty'), ('Forty', 'ParentLinks')):
        assert source('CoveringDesigns.C14_5_3.' + forbidden) not in closure(
            'CoveringDesigns.C14_5_3.' + stage), f'C14 logical order reversed: {stage}'
    # The lifting application may use only the seed lower proof and the existing
    # ordinary iterated-lifting interface. Every older component stays independent.
    lift_parts = {
        'Applications.C18103Lifts': ['Applications.C18103Lifts.Corollaries'],
        'Applications.C18103Lifts.Corollaries': ['Applications.C18103Lifts.LowerBound'],
        'Applications.C18103Lifts.LowerBound': ['C18_10_3.LowerBound', 'Multicover.Schoenheim'],
    }
    lift_sources = {source('CoveringDesigns.' + part) for part in lift_parts}
    for key, paths in closures.items():
        if key != 'c18103-lifts':
            assert not paths & lift_sources, f'Established component {key} imports C18103 lifts'
    for part, dependencies in lift_parts.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'C18103 lifts {part} imports outside its declared interface'
    assert source('CoveringDesigns.C18_10_3.Witness') not in closures['c18103-lifts'], \
        'Lifting lower bounds must not depend on the attaining witness'
    for part in ('LiftingComparison.Applications', 'LiftingComparison.Covering',
                 'LiftingComparison.Iteration', 'MulticoverLargeDefect.Family',
                 'BoundaryRank.SquareDuality', 'C18_10_3.SquareSupport'):
        assert source('CoveringDesigns.' + part) not in closures['c18103-lifts'], \
            f'C18103 lifts must avoid unused comparison/square stages: {part}'
    assert source('CoveringDesigns.BoundaryRank.SquareDuality') not in closure(
        'CoveringDesigns.C18_10_3'), 'The covering result must not import square duality'
    # Existing components cannot acquire a dependency on the new result or helpers.
    # The new result uses only the declared earlier helper interfaces.
    c18_parts = {'C18_10_3': ['C18_10_3.LowerBound', 'C18_10_3.Witness', 'Foundations.StandardAxioms'],
     'C18_10_3.Core': ['BoundaryRank.RestrictedEquality', 'TwoKMinusTwoEquality.Matrix'],
     'C18_10_3.SquareSupport': ['C18_10_3', 'BoundaryRank.SquareDuality'],
     'C18_10_3.Exceptional': ['C18_10_3.RankCases', 'Foundations.PairedSupportObstruction'],
     'C18_10_3.Incidence': ['TwoKMinusTwo.Incidence'],
     'C18_10_3.LowRows': ['C18_10_3.Incidence', 'C18_10_3.Core'],
     'C18_10_3.LowerBound': ['C18_10_3.SaturatedMatching', 'C18_10_3.Exceptional'],
     'C18_10_3.RankCases': ['C18_10_3.LowRows', 'BoundaryRank.DeficitCharging'],
     'C18_10_3.SaturatedLocal': ['C18_10_3.Incidence',
                                 'SaturatedMatching.Counting',
                                 'SaturatedMatching.Geometry'],
     'C18_10_3.SaturatedMatching': ['C18_10_3.SaturatedLocal', 'Foundations.IncidencePacking'],
     'C18_10_3.Witness': ['Foundations.Relabelling'],
     'BoundaryRank.RestrictedEquality': ['BoundaryRank.Equality'],
     'BoundaryRank.SquareDuality': ['TwoKMinusTwoEquality.Matrix', 'Foundations.SupportObstruction'],
     'Foundations.SupportObstruction': ['Foundations.Basic'],
     'Foundations.SupportDifferences': ['Foundations.SupportObstruction'],
     'Foundations.PairedSupportObstruction': ['Foundations.SupportDifferences'],
     'Foundations.IncidencePacking': ['Foundations.Basic']}
    c18_sources = {source('CoveringDesigns.' + part) for part in c18_parts}
    for key, paths in closures.items():
        if key not in ('18-10-3', 'c18103-lifts'):
            assert not paths & c18_sources, f'Established component {key} imports C18_10_3'
    for part, dependencies in c18_parts.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'C18 {part} imports outside its declared interface'
    for part in ('', '.Rank', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['18-10-3'], \
            'C18 imports the numerical C20 result or witness'
    for part in ('Completion', 'BinaryCompletion', 'IndexedIncidence', 'Capacity'):
        assert source('CoveringDesigns.BoundaryRank.' + part) not in closures['18-10-3'], \
            'C18 imports an inapplicable completion or unrelated capacity interface'
    # New matching modules have fixed declared interfaces; no existing component
    # may import them. The abstract pattern proofs exclude numerical adapters.
    matching_parts = {'AffineCapacity.Boundary': ['AffineCapacity.Basic'],
     'C60_31_3': ['C60_31_3.Bounds', 'Foundations.StandardAxioms'],
     'C60_31_3.Bounds': ['SaturatedMatching.CoverFive'],
     'C62_32_3': ['C62_32_3.Bounds', 'Foundations.StandardAxioms'],
     'C62_32_3.Bounds': ['SaturatedMatching.Endpoints',
                  'SaturatedMatching.Budget',
                  'TwoKMinusTwoTightening',
                  'TwoKMinusTwo.Construction'],
     'SaturatedMatching': ['SaturatedMatching.Exactness', 'Foundations.StandardAxioms'],
     'SaturatedMatching.Budget': ['TwoKMinusTwoCapacity.Indexed', 'AffineCapacity.Boundary'],
     'SaturatedMatching.CompleteMatching': ['SaturatedMatching.CoverPattern'],
     'SaturatedMatching.Counting': ['TwoKMinusTwo.Capacity'],
     'SaturatedMatching.CoverBudget': ['SaturatedMatching.CompleteMatching'],
     'SaturatedMatching.CoverFive': ['SaturatedMatching.CoverFour'],
     'SaturatedMatching.CoverFour': ['SaturatedMatching.CoverBudget'],
     'SaturatedMatching.CoverPattern': ['SaturatedMatching.Separation',
                                        'SaturatedMatching.Four',
                                        'SaturatedMatching.Five',
                                        'C62_32_3'],
     'SaturatedMatching.Endpoints': ['SaturatedMatching.Split'],
     'SaturatedMatching.Exactness': ['C60_31_3', 'TwoKMinusTwoCapacity.Exactness'],
     'SaturatedMatching.Five': ['SaturatedMatching.Pattern'],
     'SaturatedMatching.Four': ['SaturatedMatching.FourNormalize'],
     'SaturatedMatching.FourGroups': ['SaturatedMatching.FourSignatures'],
     'SaturatedMatching.FourNormalize': ['SaturatedMatching.Relabel',
                                         'SaturatedMatching.FourNormalized'],
     'SaturatedMatching.FourNormalized': ['SaturatedMatching.Pattern'],
     'SaturatedMatching.FourSignatures': ['SaturatedMatching.Pattern'],
     'SaturatedMatching.Geometry': ['TwoKMinusTwo.Capacity', 'C20_11_3.SaturatedLoss'],
     'SaturatedMatching.Pattern': ['BoundaryRank.IndexedIncidence'],
     'SaturatedMatching.Relabel': ['SaturatedMatching.FourGroups'],
     'SaturatedMatching.Separation': ['SaturatedMatching.Endpoints'],
     'SaturatedMatching.Split': ['SaturatedMatching.Geometry', 'SaturatedMatching.Counting']}
    matching_sources = {source('CoveringDesigns.' + part) for part in matching_parts}
    for key, paths in closures.items():
        if key not in ('saturated-matching', '18-10-3', 'c18103-lifts'):
            assert not paths & matching_sources, f'Established component {key} imports saturated matching'
    assert closures['18-10-3'] & matching_sources == {
        source('CoveringDesigns.SaturatedMatching.' + p) for p in ('Counting', 'Geometry')}, \
        'C18 imports matching machinery beyond the two generic counting/geometry interfaces'
    for part, dependencies in matching_parts.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'Matching {part} imports outside its declared interface'
    for part in ('', '.Rank', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['saturated-matching'], \
            'Saturated matching imports the numerical C20 proof or witness'
    # New capacity paths are additive; established components remain independent.
    capacity_parts = {
        'AffineCapacity.Basic': ['Foundations.Basic'],
        'AffineCapacity.Cube': ['AffineCapacity.Basic'],
        'BoundaryRank.SupportDimension': ['AffineCapacity.Cube', 'BoundaryRank.Completion'],
        'BoundaryRank.SupportCapacity': ['BoundaryRank.CloneCapacity'],
        'BoundaryRank.DeficitCharging': [],
        'BoundaryRank.IndexedIncidence': ['AffineCapacity.Basic', 'BoundaryRank.CloneCapacity', 'BoundaryRank.Completion'],
        'BoundaryRank.IndexedCounting': ['BoundaryRank.IndexedIncidence', 'BoundaryRank.DeficitCharging'],
        'BoundaryRank.Capacity': ['BoundaryRank.IndexedCounting', 'BoundaryRank.SupportDimension', 'BoundaryRank.SupportCapacity'],
        'TwoKMinusTwoCapacity.Indexed': ['BoundaryRank.Capacity'],
        'TwoKMinusTwoCapacity.Exactness': ['TwoKMinusTwoCapacity.Indexed', 'TwoKMinusTwo.Bounds', 'TwoKMinusTwo.Construction'],
        'TwoKMinusTwoCapacity': ['TwoKMinusTwoCapacity.Exactness', 'Foundations.StandardAxioms'],
        'C64_33_3.Bounds': ['TwoKMinusTwoCapacity.Exactness'],
        'C64_33_3': ['C64_33_3.Bounds', 'Foundations.StandardAxioms'],
        'C66_34_3.Bounds': ['TwoKMinusTwoCapacity.Exactness'],
        'C66_34_3': ['C66_34_3.Bounds', 'Foundations.StandardAxioms'],
        'RankSlackCapacity': ['TwoKMinusTwoCapacity', 'C64_33_3', 'C66_34_3'],
    }
    capacity_sources = {source('CoveringDesigns.' + part) for part in capacity_parts}
    for key, paths in closures.items():
        if key not in ('rank-slack-capacity', 'saturated-matching', '18-10-3', 'c18103-lifts'):
            assert not paths & capacity_sources, f'Established component {key} imports rank-slack capacity'
    assert closures['18-10-3'] & capacity_sources == {
        source('CoveringDesigns.BoundaryRank.DeficitCharging')}, \
        'C18 imports rank-slack capacity beyond integer deficit charging'
    for part, dependencies in capacity_parts.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'Capacity {part} imports outside its declared interface'
    for part in ('', '.Rank', '.SaturatedLoss', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['rank-slack-capacity'], \
            'Rank-slack capacity imports the numerical C20 proof or witness'
    tightening_parts = {
        'BoundaryRank.Completion': ['BoundaryRank.Nullity'],
        'BoundaryRank.BinaryCompletion': [],
        'BoundaryRank.CloneCapacity': ['Foundations.Intersecting'],
        'TwoKMinusTwoTightening.Incidence': ['TwoKMinusTwo.Rank'],
        'TwoKMinusTwoTightening.Endpoints': ['TwoKMinusTwoTightening.Incidence',
            'BoundaryRank.Completion', 'BoundaryRank.BinaryCompletion', 'BoundaryRank.CloneCapacity'],
        'TwoKMinusTwoTightening.Bounds': ['TwoKMinusTwoTightening.Endpoints', 'TwoKMinusC.OffsetTwo'],
        'TwoKMinusTwoTightening': ['TwoKMinusTwoTightening.Bounds', 'Foundations.StandardAxioms'],
    }
    tightening_sources = {source('CoveringDesigns.' + part) for part in tightening_parts}
    for key, paths in closures.items():
        if key not in ('two-k-minus-two-tightening', 'rank-slack-capacity', 'saturated-matching'):
            assert not paths & tightening_sources, f'Established component {key} imports checkpoint tightening'
    for part, dependencies in tightening_parts.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, f'Checkpoint {part} imports outside its declared interface'
    for part in ('', '.Rank', '.SaturatedLoss', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['two-k-minus-two-tightening'], \
            'Checkpoint imports the numerical C20 proof or witness'
    # Preserve prior components and separate the new rank/geometry/adapter paths.
    general_root = ROOT / 'CoveringDesigns/TwoKMinusCGeneral'
    general_files = {source('CoveringDesigns.TwoKMinusCGeneral'),
                     source('CoveringDesigns.Weighted.PartitionedRank')}
    for key, paths in closures.items():
        if key != 'two-k-minus-c-general':
            assert not any(p in general_files or p.is_relative_to(general_root) for p in paths), \
                f'Established component {key} imports fixed-offset generalisation'
    for part in ('', '.Rank', '.SaturatedLoss', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['two-k-minus-c-general'], \
            'Fixed-offset generalisation imports numerical C20 proof or witness'
    general_dependencies = {
        'Weighted.PartitionedRank': ['Combinatorics.WeightedPartition', 'Weighted.Matrix'],
        'TwoKMinusCGeneral.Arithmetic': ['TwoKMinusTwo.Arithmetic'],
        'TwoKMinusCGeneral.Incidence': ['C20_11_3.Incidence', 'TwoKMinusTwo.Incidence', 'TwoKMinusCGeneral.Arithmetic'],
        'TwoKMinusCGeneral.Geometry': ['C20_11_3.SaturatedAssignment', 'TwoKMinusTwo.Incidence'],
        'TwoKMinusCGeneral.Assignment': ['TwoKMinusCGeneral.Geometry', 'C20_11_3.SaturatedBudget'],
        'TwoKMinusCGeneral.Capacity': ['TwoKMinusCGeneral.Assignment', 'TwoKMinusCGeneral.Incidence', 'C20_11_3.SaturatedBudget'],
        'TwoKMinusCGeneral.Saturation': ['TwoKMinusCGeneral.Capacity'],
        'TwoKMinusCGeneral.Rank': ['Weighted.PartitionedRank', 'TwoKMinusTwo.Rank'],
        'TwoKMinusCGeneral.UniformLower': ['TwoKMinusCGeneral.Rank', 'TwoKMinusCGeneral.Saturation'],
        'TwoKMinusCGeneral.OffsetThreeArithmetic': ['TwoKMinusC.Algebra'],
        'TwoKMinusCGeneral.OffsetThreeLower': ['TwoKMinusC.LargeDefect', 'TwoKMinusCGeneral.OffsetThreeArithmetic', 'TwoKMinusCGeneral.Saturation'],
        'TwoKMinusCGeneral.Attainment': ['TwoKMinusTwo.Construction', 'PointReduction.Family'],
        'TwoKMinusCGeneral.Exactness': ['TwoKMinusCGeneral.UniformLower', 'TwoKMinusCGeneral.OffsetThreeLower', 'TwoKMinusCGeneral.Attainment'],
        'TwoKMinusCGeneral': ['TwoKMinusCGeneral.Exactness', 'Foundations.StandardAxioms'],
    }
    for part, dependencies in general_dependencies.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, \
            f'Fixed-offset {part} imports outside its declared interface'
    offset_root = ROOT / 'CoveringDesigns/TwoKMinusC'
    offset_entry = source('CoveringDesigns.TwoKMinusC')
    for key, paths in closures.items():
        if key not in ('two-k-minus-c', 'two-k-minus-c-general', 'two-k-minus-two-tightening', 'saturated-matching', '34-18-3', *C34183_LIFT_KEYS):
            assert not any(p == offset_entry or p.is_relative_to(offset_root) for p in paths), \
                f'Established component {key} imports TwoKMinusC'
    for part in ('', '.Rank', '.SaturatedLoss', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['two-k-minus-c'], \
            'TwoKMinusC imports the numerical C20 proof or witness'
    offset_dependencies = {
        'Algebra': ['MulticoverLargeDefect.LowerBound'],
        'LargeDefect': ['TwoKMinusC.Algebra', 'Multicover.Family'],
        'OffsetTwoArithmetic': ['TwoKMinusC.Algebra'],
        'OffsetTwo': ['TwoKMinusC.LargeDefect', 'TwoKMinusC.OffsetTwoArithmetic',
                      'TwoKMinusTwo.Bounds', 'TwoKMinusTwo.Construction'],
        '': ['TwoKMinusC.OffsetTwo', 'Foundations.StandardAxioms'],
    }
    for part, dependencies in offset_dependencies.items():
        module = 'CoveringDesigns.TwoKMinusC' + ('.' + part if part else '')
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, \
            f'TwoKMinusC {part or "entry"} imports outside its declared interface'
    c20_roots = (ROOT / 'CoveringDesigns/C20_11_3',
                 ROOT / 'CoveringDesigns/BoundaryRank')
    c20_entry = source('CoveringDesigns.C20_11_3')
    for key, paths in closures.items():
        if key not in ('20-11-3', 'two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c', 'two-k-minus-c-general', 'two-k-minus-two-tightening', 'rank-slack-capacity', 'saturated-matching', '18-10-3', 'c18103-lifts', '34-18-3', *C34183_LIFT_KEYS):
            assert not any(p == c20_entry or any(p.is_relative_to(r) for r in c20_roots)
                           for p in paths), f'Established component {key} imports C20_11_3'
    family_root = ROOT / 'CoveringDesigns/TwoKMinusTwo'
    family_entry = source('CoveringDesigns.TwoKMinusTwo')
    for key, paths in closures.items():
        if key not in ('two-k-minus-two', 'two-k-minus-two-equality', 'two-k-minus-c', 'two-k-minus-c-general', 'two-k-minus-two-tightening', 'rank-slack-capacity', 'saturated-matching', '18-10-3', 'c18103-lifts', '34-18-3', *C34183_LIFT_KEYS):
            assert not any(p == family_entry or p.is_relative_to(family_root) for p in paths), \
                f'Established component {key} imports TwoKMinusTwo'
    # The new family may reuse generic helpers, never the established C20 result.
    for part in ('', '.Rank', '.SaturatedLoss', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['two-k-minus-two'], \
            'TwoKMinusTwo imports the numerical C20 proof or witness'
    equality_roots = (ROOT / 'CoveringDesigns/TwoKMinusTwoEquality',)
    equality_files = {source('CoveringDesigns.TwoKMinusTwoEquality'),
                      source('CoveringDesigns.BoundaryRank.Equality')}
    for key, paths in closures.items():
        if key not in ('two-k-minus-two-equality', '18-10-3', 'c18103-lifts'):
            assert not any(p in equality_files or any(p.is_relative_to(r) for r in equality_roots)
                           for p in paths), f'Established component {key} imports equality refinement'
    for part in ('', '.Rank', '.SaturatedLoss', '.Saturated', '.LowerBound', '.Witness'):
        assert source('CoveringDesigns.C20_11_3' + part) not in closures['two-k-minus-two-equality'],             'Equality refinement imports the numerical C20 proof or witness'
    equality_dependencies = {
        'BoundaryRank.Equality': ['BoundaryRank.Nullity'],
        'TwoKMinusTwoEquality.Matrix': ['BoundaryRank.Equality'],
        'TwoKMinusTwoEquality.Rigidity': ['TwoKMinusTwoEquality.Matrix', 'TwoKMinusTwo.Rank'],
        'TwoKMinusTwoEquality.Bounds': ['TwoKMinusTwoEquality.Rigidity', 'TwoKMinusTwo.Bounds'],
        'TwoKMinusTwoEquality': ['TwoKMinusTwoEquality.Bounds', 'TwoKMinusTwo.Construction',
                                'Foundations.StandardAxioms'],
    }
    for part, dependencies in equality_dependencies.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected,             f'Equality refinement {part} imports outside its declared interface'
    family_dependencies = {
        'Arithmetic': [],
        'Incidence': ['C20_11_3.Incidence', 'TwoKMinusTwo.Arithmetic'],
        'Geometry': ['C20_11_3.SaturatedAssignment'],
        'Rank': ['TwoKMinusTwo.Incidence', 'BoundaryRank.Nullity'],
        'Capacity': ['TwoKMinusTwo.Geometry', 'TwoKMinusTwo.Incidence',
                     'C20_11_3.SaturatedBudget'],
        'Bounds': ['TwoKMinusTwo.Rank', 'TwoKMinusTwo.Capacity'],
        'Expansion': ['AffineConstructions.Transformations'],
        'AffineWeights': ['AffineConstructions.Geometry'],
        'Construction': ['TwoKMinusTwo.AffineWeights', 'TwoKMinusTwo.Expansion'],
        '': ['TwoKMinusTwo.Bounds', 'TwoKMinusTwo.Construction',
             'Foundations.StandardAxioms'],
    }
    for part, dependencies in family_dependencies.items():
        module = 'CoveringDesigns.TwoKMinusTwo' + ('.' + part if part else '')
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, \
            f'TwoKMinusTwo {part or "entry"} imports outside its declared interface'
    c20_dependencies = {
        'BoundaryRank.Signless': [],
        'BoundaryRank.Nullity': ['BoundaryRank.Signless'],
        'C20_11_3.Incidence': ['Foundations.Bounds'],
        'C20_11_3.Rank': ['C20_11_3.Incidence', 'BoundaryRank.Nullity'],
        'C20_11_3.SaturatedGeometry': ['Foundations.Links'],
        'C20_11_3.SaturatedPartition': ['Foundations.Links'],
        'C20_11_3.SaturatedAssignment': ['C20_11_3.SaturatedGeometry',
                                        'C20_11_3.SaturatedPartition'],
        'C20_11_3.SaturatedBudget': ['Foundations.Basic'],
        'C20_11_3.SaturatedLoss': ['C20_11_3.SaturatedGeometry',
                                  'C20_11_3.SaturatedPartition'],
        'C20_11_3.Saturated': ['C20_11_3.Incidence', 'C20_11_3.SaturatedAssignment',
                               'C20_11_3.SaturatedBudget', 'C20_11_3.SaturatedLoss'],
        'C20_11_3.LowerBound': ['C20_11_3.Rank', 'C20_11_3.Saturated'],
        'C20_11_3.Witness': ['Foundations.Relabelling'],
        'C20_11_3': ['C20_11_3.LowerBound', 'C20_11_3.Witness',
                     'Foundations.StandardAxioms'],
    }
    for part, dependencies in c20_dependencies.items():
        module = 'CoveringDesigns.' + part
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure('CoveringDesigns.' + dependency)
        assert closure(module) == expected, \
            f'C20_11_3 {part} imports outside its declared interface'
    degree_root = ROOT / 'CoveringDesigns/DegreeSelected'
    degree_entry = source('CoveringDesigns.DegreeSelected')
    for key, paths in closures.items():
        if key != 'degree-selected':
            assert not any(p == degree_entry or p.is_relative_to(degree_root) for p in paths), \
                f'Established component {key} imports DegreeSelected'
    geometry_root = ROOT / 'CoveringDesigns/FiniteGeometry'
    geometry_entry = source('CoveringDesigns.FiniteGeometry')
    for key, paths in closures.items():
        if key != 'finite-flat-geometry':
            assert not any(p == geometry_entry or p.is_relative_to(geometry_root) for p in paths), \
                f'Established component {key} imports FiniteGeometry'
    projective_root = ROOT / 'CoveringDesigns/ProjectiveHyperplanes'
    projective_entry = source('CoveringDesigns.ProjectiveHyperplanes')
    for key, paths in closures.items():
        if key not in ('projective-hyperplanes', 'finite-flat-geometry'):
            assert not any(p == projective_entry or p.is_relative_to(projective_root) for p in paths), \
                f'Established component {key} imports ProjectiveHyperplanes'
    averaging_root = ROOT / 'CoveringDesigns/GKPInducedAveraging'
    averaging_entry = source('CoveringDesigns.GKPInducedAveraging')
    for key, paths in closures.items():
        if key not in ('gkp-induced-averaging', 'projective-hyperplanes'):
            assert not any(p == averaging_entry or p.is_relative_to(averaging_root) for p in paths), \
                f'Established component {key} imports GKPInducedAveraging'
    induced_root = ROOT / 'CoveringDesigns/GKPInduced'
    induced_entry = source('CoveringDesigns.GKPInduced')
    for key, paths in closures.items():
        if key not in ('gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes'):
            assert not any(p == induced_entry or p.is_relative_to(induced_root) for p in paths), \
                f'Established component {key} imports GKPInduced'
    gkp_root = ROOT / 'CoveringDesigns/GKPCombination'
    gkp_entry = source('CoveringDesigns.GKPCombination')
    for key, paths in closures.items():
        if key not in ('gkp-combination', 'gkp-induced', 'gkp-induced-averaging', 'projective-hyperplanes', 'degree-selected'):
            assert not any(p == gkp_entry or p.is_relative_to(gkp_root) for p in paths), \
                f'Established component {key} imports GKPCombination'
    # Exact generic closure: examples cannot leak affine numerical or lower bounds
    # into reusable construction theorems, even through an intermediate helper.
    chvatal_root = ROOT / 'CoveringDesigns/Chvatal'
    chvatal_entry = source('CoveringDesigns.Chvatal')
    for key, paths in closures.items():
        if key != 'chvatal':
            assert not any(p == chvatal_entry or p.is_relative_to(chvatal_root) for p in paths), \
                f'Established component {key} imports Chvatal'
    turan_root = ROOT / 'CoveringDesigns/Turan'
    turan_entry = source('CoveringDesigns.Turan')
    basic = source('CoveringDesigns.Foundations.Basic')
    duality = source('CoveringDesigns.Turan.Duality')
    for key, paths in closures.items():
        if key not in ('turan-duality', 'turan', 'de-caen'):
            assert not any(p == turan_entry or p.is_relative_to(turan_root) for p in paths), \
                f'Established component {key} imports the Turan foundation'
    decaen_root = ROOT / 'CoveringDesigns/DeCaen'
    decaen_entry = source('CoveringDesigns.DeCaen')
    for key, paths in closures.items():
        if key != 'de-caen':
            assert not any(p == decaen_entry or p.is_relative_to(decaen_root) for p in paths), \
                f'Established component {key} imports DeCaen'
    # The numerical consequences and the new structural component have
    # independent dependency closures. Existing results cannot acquire a
    # dependency on either strand through a shared import.
    discovery_keys = ('14-8-5', '59-17-5', '66-18-5', '79-22-5', '87-23-5', '98-22-5')
    new_roots = ['CoveringDesigns.C14_8_5', 'CoveringDesigns.C59_17_5', 'CoveringDesigns.C66_18_5', 'CoveringDesigns.C79_22_5', 'CoveringDesigns.C87_23_5', 'CoveringDesigns.C98_22_5', 'CoveringDesigns.LabelledCliques']
    for key, paths in closures.items():
        if key in (*discovery_keys, 'labelled-cliques'):
            continue
        for path in paths:
            # C14 and C19 reuse only the generic actual-occurrence extension count.
            if key in ('14-5-3', '19-9-3', *C1453_LIFT_KEYS) and path == source('CoveringDesigns.LabelledCliques.Extensions'):
                continue
            module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
            assert not any(module == name or module.startswith(name + '.') for name in new_roots), \
                f'Established component {key} imports a new discovery consequence: {path}'
    structural_allowed = closure('CoveringDesigns.Multicover.Family') | \
        closure('CoveringDesigns.HorsleySingh.Parameters')
    for path in set().union(closure('CoveringDesigns.LabelledCliques.Extensions')):
        assert path in structural_allowed or path == source('CoveringDesigns.LabelledCliques') or \
            path.is_relative_to(ROOT / 'CoveringDesigns/LabelledCliques'), \
            f'Labelled cliques import rank, selection or an application: {path}'
    for part in ('Extensions',):
        allowed = closure('CoveringDesigns.Multicover.Counting') | \
            {source('CoveringDesigns.LabelledCliques.Extensions'),
             source('CoveringDesigns.LabelledCliques.Propagation')}
        assert closure('CoveringDesigns.LabelledCliques.' + part) <= allowed, \
            f'Labelled {part} must use only occurrence links/counting'
    for key in ():
        for path in closures[key]:
            assert path != source('CoveringDesigns.LabelledCliques') and not \
                path.is_relative_to(ROOT / 'CoveringDesigns/LabelledCliques'), \
                f'Numerical consequence {key} imports labelled-clique propagation'
    large_algebra = 'CoveringDesigns.LargeDefect.Algebra'
    assert closure(large_algebra) == {source(large_algebra)}, \
        'Large-defect coefficient algebra must be independent of covering-design modules'
    large_core = closure('CoveringDesigns.LargeDefect.LowerBound')
    for name in ('LargeDefect.Pairs', 'LargeDefect.Examples', 'HigherIncidence.Examples',
                 'CaroTuza.Examples', 'Horsley.LowerBound', 'HorsleySingh.LowerBound'):
        assert source('CoveringDesigns.' + name) not in large_core, \
            f'Large-defect core imports a specialised theorem or example: {name}'
    assert source('CoveringDesigns.Applications.ZeroDefect') not in set().union(closure('CoveringDesigns.LargeDefect.Algebra'), closure('CoveringDesigns.LargeDefect.LowerBound'), closure('CoveringDesigns.LargeDefect.Selection')), \
        'Large-defect foundations must be independent of ZeroDefect'
    for path in closures['caro-tuza']:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        assert module == 'CoveringDesigns.CaroTuza' or module.startswith('CoveringDesigns.CaroTuza.'), \
            f'Caro-Tuza selection must be independent of other covering-design modules: {path}'
    function = 'CoveringDesigns.CaroTuza.Function'
    assert closure(function) == {source(function)}, \
        'Caro-Tuza scalar estimates must be independent of graph selection'
    assert source('CoveringDesigns.CaroTuza.Examples') not in closure('CoveringDesigns.CaroTuza.Selection'), \
        'Caro-Tuza selection must be independent of examples'
    partition = 'CoveringDesigns.Combinatorics.WeightedPartition'
    assert closure(partition) == {source(partition)}, \
        'Weighted partition must be independent of all covering-design modules'
    weighted_matrix = 'CoveringDesigns.Weighted.Matrix'
    assert closure(weighted_matrix) == {source(weighted_matrix), source('CoveringDesigns.Horsley.Matrix')}, \
        'Weighted matrix foundations must be independent of covering definitions and counting'
    weighted_counting = closure('CoveringDesigns.Weighted.Counting')
    forbidden_counting = ('Horsley', 'HorsleySingh', 'Applications',
                          'Weighted.Matrix', 'Weighted.Pairs', 'Weighted.Examples')
    for path in weighted_counting:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        assert not any(module == 'CoveringDesigns.' + name or
                       module.startswith('CoveringDesigns.' + name + '.')
                       for name in forbidden_counting), \
            f'Weighted counting imports matrix or covering-specific machinery: {path}'
    assert source('CoveringDesigns.Applications.ZeroDefect') not in closures['weighted'], \
        'Weighted foundations must be independent of ZeroDefect'
    binomial = 'CoveringDesigns.HigherIncidence.Binomial'
    assert closure(binomial) == {source(binomial)}, \
        'General binomial inversion must be independent of covering-design modules'
    general_core = closure('CoveringDesigns.HigherIncidence.LowerBound')
    for name in ('Horsley.LowerBound', 'HorsleySingh.LowerBound',
                 'HigherIncidence.Examples', 'Applications.ZeroDefect'):
        assert source('CoveringDesigns.' + name) not in general_core, \
            f'General subset-incidence core imports a specialised theorem or application: {name}'
    assert source('CoveringDesigns.Applications.ZeroDefect') not in set().union(closure('CoveringDesigns.HigherIncidence.Binomial'), closure('CoveringDesigns.HigherIncidence.Counting'), closure('CoveringDesigns.HigherIncidence.LowerBound'), closure('CoveringDesigns.HigherIncidence.Matrices'), closure('CoveringDesigns.HigherIncidence.Parameters'), closure('CoveringDesigns.HigherIncidence.Subsets')), \
        'General subset incidence must be independent of ZeroDefect'
    c11, c12, c13 = (closures[key] for key in ('11-5-2', '12-6-3', '13-7-4'))
    assert c11 <= c12, 'GPPT must import the standalone Stanton component'
    for key, info in COMPONENTS.items():
        forbidden = [publication_boundaries[other] for other in info['independent_of'] if other in publication_boundaries]
        for path in closures[key]:
            module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
            assert not any(module == entry or module.startswith(entry + '.') for entry in forbidden), \
                f'{key} imports an independent component: {path}'
    assert source('CoveringDesigns.C12_6_3.Structural.Reduction') in c13
    assert source('CoveringDesigns.C11_5_2.Stanton') in c13
    catalogue_modules = {source('CoveringDesigns.C12_6_3.' + name) for name in (
        'Catalogue', 'CatalogueBridge', 'Classification',
        'Structural.CompletionEncoding', 'Structural.CompletionData',
        'Structural.CompletionSupport', 'Structural.CompletionChecks',
        'Structural.Completions')}
    structural = closure('CoveringDesigns.C12_6_3.Structural.Reduction')
    for name, paths in [('GPPT structural reduction', structural), ('C13', c13)]:
        unexpected = paths & catalogue_modules
        assert not unexpected, f'{name} imports catalogue/classification modules: {sorted(unexpected)}'
    retained = [closure(entry) for info in COMPONENTS.values()
                for entry in info.get('verification_entries', [])]
    paths = set().union(*closures.values(), *retained) | set((ROOT / 'audits').glob('*.lean'))
    for path in paths:
        text = path.read_text()
        assert not {'Explorations', 'Checked'}.intersection(path.parts), path
        assert not re.search(r'\b(?:sorry|admit)\b|^\s*(?:axiom|unsafe)\b', text, re.M), path
        assert not re.search(r'\b(?:native_decide|bv_decide|bv_check)\b|decide\s*\+native', text), path
    for path in (ROOT / 'CoveringDesigns/Foundations').glob('*.lean'):
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        assert not any({'C11_5_2', 'C12_5_2', 'C12_6_3', 'C13_7_4', 'Explorations'}.intersection(p.parts)
                       for p in closure(module)), path
    multicover_shared = {
        'CoveringDesigns.Foundations.Basic', 'CoveringDesigns.Foundations.Intersecting',
        'CoveringDesigns.Foundations.Links', 'CoveringDesigns.Foundations.Bounds',
        'CoveringDesigns.Schoenheim.LowerBound',
        'CoveringDesigns.HorsleySingh.SubsetLinks',
    }
    for path in closures['multicover']:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        assert (module == 'CoveringDesigns.Multicover' or
                module.startswith('CoveringDesigns.Multicover.') or module in multicover_shared), \
            f'Multicover imports a specialised result or application: {path}'
    for name in ('Basic', 'Links'):
        permitted = {source('CoveringDesigns.Multicover.' + part) for part in ('Basic', 'Links')}
        permitted |= {source('CoveringDesigns.Foundations.' + part) for part in ('Basic', 'Intersecting')}
        assert closure('CoveringDesigns.Multicover.' + name) <= permitted, \
            f'Multicover {name} must be independent of bounds and compatibility adapters'
    multicover_core = closure('CoveringDesigns.Multicover.Schoenheim')
    for name in ('Multicover.Family', 'Multicover.Multiset', 'Multicover.Examples',
                 'Multicover', 'HorsleySingh.SubsetLinks'):
        assert source('CoveringDesigns.' + name) not in multicover_core, \
            f'Multicover core imports a compatibility adapter or example: {name}'
    indexed_incidence_core = closure('CoveringDesigns.MulticoverIncidence.LowerBound')
    for name in ('MulticoverIncidence.Family', 'MulticoverIncidence.Examples',
                 'Multicover.Family', 'Multicover.Multiset', 'Multicover.Examples', 'Multicover',
                 'HigherIncidence.LowerBound', 'HigherIncidence.Examples',
                 'Horsley.LowerBound', 'HorsleySingh.LowerBound', 'Applications.ZeroDefect'):
        assert source('CoveringDesigns.' + name) not in indexed_incidence_core, \
            f'Indexed incidence core imports an adapter, ordinary covering theorem or application: {name}'
    for name in ('Counting', 'Parameters'):
        numeric_core = closure('CoveringDesigns.MulticoverIncidence.' + name)
        for forbidden in ('MulticoverIncidence.Matrices', 'HigherIncidence.Matrices',
                          'HorsleySingh.Matrices', 'Weighted.Matrix'):
            assert source('CoveringDesigns.' + forbidden) not in numeric_core, \
                f'Indexed incidence {name} must be independent of matrices: {forbidden}'
    for name in ('Horsley.LowerBound', 'HorsleySingh.LowerBound', 'HigherIncidence.Examples',
                 'Multicover.Examples', 'Applications.ZeroDefect'):
        assert source('CoveringDesigns.' + name) not in set().union(closure('CoveringDesigns.MulticoverIncidence.Counting'), closure('CoveringDesigns.MulticoverIncidence.Family'), closure('CoveringDesigns.MulticoverIncidence.LowerBound'), closure('CoveringDesigns.MulticoverIncidence.Matrices'), closure('CoveringDesigns.MulticoverIncidence.Parameters')), \
            f'Indexed incidence imports an unrelated specialised theorem or example: {name}'
    indexed_large_core = closure('CoveringDesigns.MulticoverLargeDefect.LowerBound')
    for name in ('MulticoverLargeDefect.Family', 'MulticoverLargeDefect.Examples',
                 'MulticoverIncidence.Family', 'MulticoverIncidence.Examples',
                 'Multicover.Family', 'Multicover.Multiset', 'Multicover.Examples', 'Multicover',
                 'HigherIncidence.LowerBound', 'LargeDefect.Selection', 'LargeDefect.LowerBound',
                 'LargeDefect.Pairs', 'LargeDefect.Examples'):
        assert source('CoveringDesigns.' + name) not in indexed_large_core, \
            f'Indexed large-defect core imports an ordinary theorem, adapter or example: {name}'
    indexed_large_counting = closure('CoveringDesigns.MulticoverLargeDefect.Counting')
    for path in indexed_large_counting:
        module = '.'.join(path.relative_to(ROOT).with_suffix('').parts)
        assert not (module.startswith('CoveringDesigns.CaroTuza.') or
                    module in ('CoveringDesigns.MulticoverLargeDefect.Selection',
                               'CoveringDesigns.MulticoverIncidence.Matrices',
                               'CoveringDesigns.HigherIncidence.Matrices',
                               'CoveringDesigns.Weighted.Matrix')), \
            f'Indexed large-defect counting must be independent of selection and rank: {path}'
    for name in ('LargeDefect.Pairs', 'LargeDefect.Examples', 'HigherIncidence.Examples',
                 'MulticoverIncidence.Examples', 'Multicover.Examples', 'CaroTuza.Examples',
                 'Horsley.LowerBound', 'HorsleySingh.LowerBound', 'Applications.ZeroDefect'):
        assert source('CoveringDesigns.' + name) not in closures['multicover-large-defect'], \
            f'Indexed large-defect component imports an unrelated theorem or example: {name}'
    # Construction foundations may reuse only the established basic definitions and relabelling.
    affine_allowed = {source('CoveringDesigns.Foundations.' + name)
                      for name in ('Basic', 'Relabelling')}
    for name in ('Transformations', 'Geometry'):
        module = 'CoveringDesigns.AffineConstructions.' + name
        affine_allowed.add(source(module))
        assert closure(module) == affine_allowed, \
            f'Affine {name} imports a specialised bound, example or later construction: {module}'
    # Lemma 9 arithmetic may use only the existing Schonheim recurrence.
    # Exact designs: numerical counting and binomial cores have no rank dependency.
    exact_design_dependencies = {'Basic': ['CoveringDesigns.Multicover.Links'], 'Counting': ['CoveringDesigns.ExactDesign.Basic', 'CoveringDesigns.Multicover.Schoenheim']}
    for part, dependencies in exact_design_dependencies.items():
        module = 'CoveringDesigns.ExactDesign' + ('.' + part if part else '')
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure(dependency)
        assert closure(module) == expected, \
            f'Exact design {part or "entry"} imports an unrelated theorem or example'
    # PointReduction: exact local module boundaries preserve the intended separation.
    point_reduction_dependencies = {'Basic': ['CoveringDesigns.Multicover.Basic'],
 'Bounds': ['CoveringDesigns.PointReduction.Basic', 'CoveringDesigns.Multicover.Links'],
 'Family': ['CoveringDesigns.PointReduction.Bounds', 'CoveringDesigns.Multicover.Family'],
 'Examples': ['CoveringDesigns.PointReduction.Family'],
 '': ['CoveringDesigns.PointReduction.Basic',
      'CoveringDesigns.PointReduction.Bounds',
      'CoveringDesigns.PointReduction.Family',
      'CoveringDesigns.PointReduction.Examples']}
    for part, dependencies in point_reduction_dependencies.items():
        module = 'CoveringDesigns.PointReduction' + ('.' + part if part else '')
        expected = {source(module)}
        for dependency in dependencies:
            expected |= closure(dependency)
        assert closure(module) == expected, \
            f'PointReduction {part or "entry"} imports an unrelated theorem or example'
    # BaseAffine: exact local module boundaries preserve the intended separation.
    return closures


def check_c18103_witness(data_path=Path('data/c18103-historical-witness.json'),
                         lean_path=Path('lean/CoveringDesigns/C18_10_3/Witness.lean')):
    """Integrity and transcription check only; Lean proves the covering claims."""
    from hashlib import sha256
    from itertools import combinations

    data = json.loads(data_path.read_text())
    assert data['parameters'] == [18, 10, 3], 'C18 witness parameters'
    blocks = data['blocks_one_based']
    assert len(blocks) == 12, 'C18 witness block count'
    assert all(len(b) == 10 and len(set(b)) == 10 for b in blocks), 'C18 block sizes'
    assert all(type(x) is int and 1 <= x <= 18 for b in blocks for x in b), 'C18 labels'
    raw_hash = sha256(bytes(x for b in blocks for x in b)).hexdigest()
    assert raw_hash == '173e0a39baa3814f25da9156a861600b0a791ff4437708d55049c85698b3d28a', \
        'C18 historical ordered block bytes changed'
    assert data['source_artefact']['encoding']['raw_sha256'] == raw_hash, 'C18 raw provenance'
    assert data['source_artefact']['licence'] == \
        'CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository.', 'C18 licence'
    assert len({frozenset(b) for b in blocks}) == 12, 'C18 repeated block'
    assert all(any(set(t) <= set(b) for b in blocks)
               for t in combinations(range(1, 19), 3)), 'C18 uncovered triple'
    text = lean_path.read_text().split('def knownBlocks12_18_10_3', 1)[1].split(
        '/-- Distinctness', 1)[0]
    lean_blocks = [[int(x) for x in re.findall(r'\d+', b)]
                   for b in re.findall(r'\{([^{}]+)\}', text)]
    assert lean_blocks == [[x - 1 for x in b] for b in blocks], 'C18 Lean transcription'


def check_manifests():
    for manifest in Path('coverings').glob('*/inputs.json'):
        for item in json.loads(manifest.read_text())['inputs']:
            assert sha(Path(item['path'])) == item['sha256'], item['path']
        if manifest.parent.name == '18-10-3':
            check_c18103_witness()
        if manifest.parent.name == '19-9-3':
            from check_c1993_witness import check
            check()
        if manifest.parent.name == '12u-plus-1-4-3':
            from check_quadruple_data import check
            from quadruple_data import generate_bases, generate_witnesses, generate_small_cover
            check()
            projections = generate_bases()
            projections.update(generate_small_cover())
            projections.update(generate_witnesses(range(3, 9)))
            for path, expected in projections.items():
                assert path.read_text() == expected, f'Stale quadruple projection: {path}'
        if manifest.parent.name == '14-5-3':
            from check_c1453_witness import check
            check()
        if manifest.parent.name == '34-18-3':
            from check_c34183_witness import check
            check()


def audit_name(key):
    return COMPONENTS[key].get('audit_name', 'c' + key.split('-')[0] + '-audit')


def explicit_theorem(key):
    namespace = COMPONENTS[key].get('audit_namespace', 'CoveringDesigns.Audit' + key.split('-')[0])
    return COMPONENTS[key].get('explicit_theorem', namespace + '.covering_number_explicit')


def principal_theorem(key):
    return COMPONENTS[key].get('principal_theorem',
                               'CoveringDesigns.covering_number_' + key.replace('-', '_'))


def audit_source(key):
    filename = COMPONENTS[key].get('audit_file', 'C' + key.replace('-', '_') + '.lean')
    return ROOT / 'audits' / filename


def verification_plan(keys, memory_mib):
    """A shared serial compiler/audit plan for the library and C13 entry points."""
    entries = ['CoveringDesigns'] if len(keys) == len(COMPONENTS) else [COMPONENTS[k]['entry'] for k in keys]
    entries += [entry for key in keys for entry in COMPONENTS[key].get('verification_entries', [])]
    plan = {}
    for module in module_order(entries):
        output = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
        plan['build-' + module] = ('build', ['lake', '-d', 'lean', 'env', 'lean',
                                            f'-M{memory_mib}', '-o', str(output), str(source(module))])
    for key in keys:
        name = audit_name(key)
        assert name not in plan, f'Duplicate audit name: {name}'
        plan[name] = ('audit',
            ['lake', '-d', 'lean', 'env', 'lean', f'-M{memory_mib}', str(audit_source(key))])
    if len(keys) == len(COMPONENTS):
        plan['all-audit'] = ('audit', ['lake', '-d', 'lean', 'env', 'lean',
                                    f'-M{memory_mib}', str(ROOT / 'audits/All.lean')])
    return plan


def record_path(prefix, name):
    return Path('results') / f'{prefix}-{name}.run.json'


def successful_run(prefix, name, kind, command, current, *, memory_guard=True):
    path = record_path(prefix, name)
    record = json.loads(path.read_text())
    assert record['returncode'] == 0 and not record['watchdog_timeout'], path
    assert record['command'] == command, f'Unexpected recorded command: {path}'
    memory_mib = int(next(arg[2:] for arg in command if arg.startswith('-M')))
    expected_guard = memory_mib if memory_guard else None
    assert record['memory_guard_mib'] == expected_guard, f'Unexpected memory guard: {path}'
    executed = record['executed_command']
    if memory_guard:
        assert executed[1:] == ['scripts/run_memory_guard.py', '--mib', str(memory_mib), *command], path
    else:
        assert executed == command, f'Unexpected unguarded command: {path}'
    assert not record.get('interrupted_signal'), f'Interrupted command: {path}'
    validate_snapshot(record, current)
    for script in RUNNER_INPUTS:
        assert record['source_hashes'].get(str(script)) == sha(script), f'Changed verification script: {script}'
    log = Path('results') / f'{prefix}-{name}.log'
    assert record['log_sha256'] == sha(log), f'Changed build/audit log: {log}'
    if kind == 'build':
        output = Path(command[command.index('-o') + 1])
        assert record.get('output_sha256', {}).get(str(output)) == sha(output), f'Changed compiled module: {output}'
    return {'record': str(path), 'log': str(log), 'log_sha256': sha(log),
            'command': command, 'elapsed_seconds': record['elapsed_seconds'],
            'memory_guard_mib': record['memory_guard_mib']}


def axioms(log, theorem):
    if re.search(r"'" + re.escape(theorem) + r"' does not depend on any axioms", log):
        return []
    match = re.search(r"'" + re.escape(theorem) + r"' depends on axioms: \[([^\]]*)\]", log)
    assert match, f'Theorem missing from successful audit: {theorem}'
    items = [a.strip() for a in match[1].split(',') if a.strip()]
    assert set(items) <= ORDINARY, f'Nonstandard axioms in {theorem}: {items}'
    return items


def component_axioms(key, log):
    """Validate every registered contract and its foundational-axiom policy.

    This is the same policy used when constructing a verification record.
    Keeping it independent of process execution lets tests exercise every
    omitted contract and axiom combination without replaying the compiler.
    Command, fingerprint and record validation remain in verification_record.
    """
    info = COMPONENTS[key]
    explicit = explicit_theorem(key)
    checked = {t: axioms(log, t) for t in info['theorems'] + info['milestones'] + [explicit]}
    principal = principal_theorem(key)
    assert set(checked[principal]) == set(checked[explicit]) == ORDINARY, principal
    return checked


def verification_record(keys, prefix, plan, current, closures, lean_version, *, memory_guard=True):
    """Revalidate every command and theorem before constructing a summary."""
    records = {name: successful_run(prefix, name, kind, command, current, memory_guard=memory_guard)
               for name, (kind, command) in plan.items()}
    components = {}
    for key in keys:
        info = COMPONENTS[key]
        log = Path(records[audit_name(key)]['log']).read_text()
        checked = component_axioms(key, log)
        principal = principal_theorem(key)
        components[key] = {**info, 'source_closure': sorted(map(str, closures[key])),
                           'axioms': checked[principal], 'audited_theorem_axioms': checked,
                           'native_assertion_count': 0}
    if 'all-audit' in records:
        log = Path(records['all-audit']['log']).read_text()
        for key in keys:
            assert set(axioms(log, principal_theorem(key))) == ORDINARY
    check_manifests()
    assert not changed_paths(current, snapshot()), 'Proof inputs changed while recording the audit'
    return {
        'recorded_utc': datetime.now(timezone.utc).isoformat(),
        'lean_version': lean_version,
        'components': components,
        'no_admissions_or_custom_mathematical_axioms': True,
        'no_native_assertions': True,
        'dependency_boundaries_checked': True,
        'proof_inputs_unchanged': True,
        'proof_input_sha256': current,
        'verification_script_sha256': {str(p): sha(p) for p in RUNNER_INPUTS},
        'verification_runs': records,
        'trust_scope': 'Each audited principal theorem and its explicit restatement uses exactly propext, Classical.choice, and Quot.sound. Finite proof computations are checked by the Lean kernel.'}


def main(*, only_c13=False):
    """Compatibility entry points share the CLI's recorded workflow."""
    os.chdir(Path(__file__).resolve().parents[1])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', default=only_c13)
    parser.add_argument('--component', choices=list(COMPONENTS),
                        default='13-7-4' if only_c13 else None)
    parser.add_argument('--resume', nargs='?', const='latest',
                        help='reuse validated steps from the latest or named run')
    parser.add_argument('--build-timeout', type=float)
    parser.add_argument('--audit-timeout', type=float)
    parser.add_argument('--memory-mib', type=int)
    parser.add_argument('--memory-guard', action=argparse.BooleanOptionalAction, default=None)
    args = parser.parse_args()
    for value in (args.build_timeout, args.audit_timeout, args.memory_mib):
        if value is not None and (not math.isfinite(value) or value <= 0):
            parser.error('time and memory limits must be positive and finite')
    from covering_cli import main as cli_main

    target = args.component or 'all'
    command = ['verify' if args.verify or args.resume else 'audit', target]
    if args.resume:
        command.extend(['--resume', args.resume])
    for name in ('build_timeout', 'audit_timeout', 'memory_mib'):
        if getattr(args, name) is not None and command[0] == 'verify':
            command.extend(['--' + name.replace('_', '-'), str(getattr(args, name))])
    if args.memory_guard is not None and command[0] == 'verify':
        command.append('--memory-guard' if args.memory_guard else '--no-memory-guard')
    raise SystemExit(cli_main(command))


if __name__ == '__main__':
    main()
