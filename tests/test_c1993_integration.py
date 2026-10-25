"""New contract, dependency and transcription controls; no mathematical claims."""
from pathlib import Path
import copy
import json
import re
import tempfile
import unittest
from unittest.mock import patch

from workflow_fixtures import audit, memory_tree, source_headers
from check_c1993_witness import check


def public_names(path):
    # These sources use ordinary block comments; erase nested comments as well.
    text, depth, pos, clean = path.read_text(), 0, 0, []
    while pos < len(text):
        if text.startswith('/-', pos):
            depth += 1
            pos += 2
        elif depth and text.startswith('-/', pos):
            depth -= 1
            pos += 2
        elif not depth and text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        else:
            if not depth or text[pos] == '\n':
                clean.append(text[pos])
            pos += 1
    stack, names = [], set()
    for line in ''.join(clean).splitlines():
        opening = re.match(r'^(namespace|section)\s*(\S*)', line)
        if opening:
            stack.append(opening.groups())
        elif re.match(r'^end(?:\s|$)', line) and stack:
            stack.pop()
        decl = re.match(r'^(?:@\[[^\]]+\]\s*)?theorem\s+([\w.]+)', line)
        if decl:
            ns = '.'.join(n for kind, n in stack if kind == 'namespace')
            if '.Internal' not in ns:
                names.add(ns + '.' + decl[1])
    return names


class SevenC1993Integration(unittest.TestCase):
    def test_complete_public_contract_and_axiom_audits(self):
        sources = {key: [] for key in audit.SEVEN_C1993_KEYS}
        for module in audit.SEVEN_C1993_IMPORTS:
            key = ('seven-block' if module in ('CoveringDesigns.SevenBlock',
                    'CoveringDesigns.SevenBlock.Stanton') else
                   'seven-block-core' if '.SevenBlock.' in module else '19-9-3')
            sources[key].append(audit.source(module))
        for key, paths in sources.items():
            names = set().union(*(public_names(p) for p in paths))
            info = audit.COMPONENTS[key]
            self.assertEqual(names, set(info['theorems'] + info['milestones']))
            text = audit.audit_source(key).read_text()
            for name in names:
                with self.subTest(component=key, theorem=name):
                    self.assertRegex(text, r'#check \(@' + re.escape(name) + r'\s*:')
                    self.assertIn('#guard_standard_axioms ' + name, text)
                    self.assertIn('#print axioms ' + name, text)

    def test_core_and_parent_omit_stanton_and_fifteen_is_independent(self):
        audit.check_sources()
        for key in ('seven-block-core', '19-9-3'):
            closure = audit.closure(audit.COMPONENTS[key]['entry'])
            for module in ('SevenBlock.Stanton', 'SevenBlock', 'C11_5_2.Classification'):
                self.assertNotIn(audit.source('CoveringDesigns.' + module), closure)
        fifteen = audit.closure('CoveringDesigns.C19_9_3.Fifteen')
        self.assertFalse(any('SevenBlock' in p.parts for p in fifteen))
        self.assertNotIn(audit.source('CoveringDesigns.C19_9_3.LowerBound'), fifteen)
        self.assertIn(audit.source('CoveringDesigns.C11_5_2.Classification'),
                      audit.closure('CoveringDesigns.SevenBlock'))

    def test_rejects_reverse_and_unapproved_direct_imports(self):
        root = memory_tree(source_headers(whole=True))
        with patch.object(audit, 'ROOT', root / 'lean'):
            for module, dependency, diagnostic in (
                ('C11_5_2', 'SevenBlock.Templates', 'Established component'),
                ('C18_10_3', 'C19_9_3.Witness', 'Established component'),
                ('SevenBlock.Core', 'SevenBlock.Stanton', 'direct interface'),
                ('C19_9_3.MinimumLinks', 'SevenBlock.Stanton', 'direct interface'),
                ('C19_9_3.Fifteen', 'SevenBlock.Core', 'direct interface'),
                ('C19_9_3.WeakCompletion', 'C19_9_3.Fifteen', 'direct interface'),
                ('C19_9_3.Witness', 'C18_10_3.Witness', 'direct interface')):
                with self.subTest(module=module, dependency=dependency):
                    path = audit.source('CoveringDesigns.' + module)
                    original = path.read_text()
                    path.write_text(original + 'import CoveringDesigns.' + dependency + '\n')
                    try:
                        with self.assertRaisesRegex(AssertionError, diagnostic):
                            audit.check_sources()
                    finally:
                        path.write_text(original)

    def test_short_main_chain_and_retained_verification_entries(self):
        lower = audit.closure('CoveringDesigns.C19_9_3.LowerBound')
        for module in ('Fifteen', 'Completion', 'ColumnWeights', 'FanoBudgets',
                       'BudgetTools', 'TwoSingleExclusion', 'FourSingleExclusion'):
            self.assertNotIn(audit.source('CoveringDesigns.C19_9_3.' + module), lower)
        self.assertFalse(any('Incidence' in p.parts or 'MulticoverIncidence' in p.parts
                             for p in lower))
        plan = audit.verification_plan(['19-9-3'], 16384)
        names = list(plan)
        for module in audit.COMPONENTS['19-9-3']['verification_entries']:
            for path in audit.closure(module):
                name = 'build-' + str(path.relative_to(audit.ROOT)).removesuffix('.lean').replace('/', '.')
                self.assertIn(name, names)
                self.assertLess(names.index(name), names.index(audit.audit_name('19-9-3')))
        self.assertEqual(len(names), len(set(names)))

    def test_retained_audit_roots_cannot_silently_disappear(self):
        info = {**audit.COMPONENTS['19-9-3'], 'verification_entries': []}
        with patch.dict(audit.COMPONENTS, {'19-9-3': info}):
            with self.assertRaisesRegex(AssertionError, 'must still be freshly compiled'):
                audit.check_sources()

    def test_retained_sources_keep_admission_and_native_checks(self):
        root = memory_tree(source_headers(whole=True))
        with patch.object(audit, 'ROOT', root / 'lean'):
            for module in ('Fifteen', 'Completion', 'ColumnWeights', 'FanoBudgets',
                           'BudgetTools', 'TwoSingleExclusion', 'FourSingleExclusion'):
                path = audit.source('CoveringDesigns.C19_9_3.' + module)
                original = path.read_text()
                for tactic in ('sorry', 'native_decide'):
                    with self.subTest(module=module, tactic=tactic):
                        path.write_text(original + f'example : True := by {tactic}\n')
                        try:
                            with self.assertRaisesRegex(AssertionError, re.escape(str(path))):
                                audit.check_sources()
                        finally:
                            path.write_text(original)

    def test_principal_axioms_are_exact_and_reject_extra_axioms(self):
        for key in audit.SEVEN_C1993_KEYS:
            info = audit.COMPONENTS[key]
            names = set(info['theorems'] + info['milestones'] + [audit.explicit_theorem(key)])
            log = '\n'.join("'" + n + "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                            for n in names)
            audit.component_axioms(key, log)
            for replacement in ('propext, Classical.choice',
                                'propext, Classical.choice, Quot.sound, invented'):
                broken = log.replace("'" + audit.principal_theorem(key) +
                    "' depends on axioms: [propext, Classical.choice, Quot.sound]",
                    "'" + audit.principal_theorem(key) + "' depends on axioms: [" + replacement + ']')
                with self.assertRaises(AssertionError):
                    audit.component_axioms(key, broken)

    def test_retained_witness_and_negative_transcription_controls(self):
        result = check()
        self.assertEqual(result['covered_triples'], 969)
        original = json.loads(Path('data/c1993-belic-witness.json').read_text())
        with tempfile.TemporaryDirectory() as tmp:
            data_path = Path(tmp) / 'data.json'
            for kind in ('label', 'missing', 'duplicate', 'credit', 'reordered'):
                data = copy.deepcopy(original)
                if kind == 'label':
                    data['blocks_one_based'][0][0] = 20
                elif kind == 'missing':
                    data['blocks_one_based'].pop()
                elif kind == 'duplicate':
                    data['blocks_one_based'][1] = data['blocks_one_based'][0]
                elif kind == 'credit':
                    data['source_artefact']['construction_credit'] = 'Incorrect credit'
                else:
                    data['blocks_one_based'][0].reverse()
                data_path.write_text(json.dumps(data))
                with self.subTest(mutation=kind), self.assertRaises(AssertionError):
                    check(data_path=data_path)
            lean_path = Path(tmp) / 'Witness.lean'
            lean = audit.source('CoveringDesigns.C19_9_3.Witness').read_text()
            literal = re.search(r'\{[\d, ]+\}', lean).group()
            lean_path.write_text(lean.replace(literal, '{0}', 1))
            with self.assertRaisesRegex(AssertionError, 'Lean transcription'):
                check(lean_path=lean_path)
            retained = Path(tmp) / 'blocks.txt'
            retained.write_text('changed retained input\n')
            with self.assertRaisesRegex(AssertionError, 'original retained block list'):
                check(retained_path=retained)


if __name__ == '__main__':
    unittest.main()
