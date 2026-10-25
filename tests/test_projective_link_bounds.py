"""Contract/dependency policy tests for one new component; no mathematical claims."""
from pathlib import Path
import re
import unittest
from unittest.mock import patch

from workflow_fixtures import audit, memory_tree, source_headers

KEY = 'projective-link-bounds'
PREFIX = 'CoveringDesigns.ProjectiveLinkBounds'


def declared_theorems(path):
    # This component uses unannotated theorem declarations and named namespaces.
    stack, names = [], set()
    text = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    for line in text.splitlines():
        opening = re.match(r'^(namespace|section)\s*(\S*)', line)
        if opening:
            stack.append(opening.groups())
        elif re.match(r'^end(?:\s|$)', line) and stack:
            stack.pop()
        decl = re.match(r'^theorem\s+([\w.]+)', line)
        if decl:
            names.add('.'.join(n for kind, n in stack if kind == 'namespace') + '.' + decl[1])
    return names


class ProjectiveLinkBoundsIntegration(unittest.TestCase):
    def test_all_public_contracts_and_axioms_are_audited(self):
        names = set().union(*(declared_theorems(audit.source(module))
                              for module in audit.PROJECTIVE_LINK_IMPORTS))
        info = audit.COMPONENTS[KEY]
        self.assertEqual(names, set(info['theorems']))
        text = audit.audit_source(KEY).read_text()
        for name in names:
            with self.subTest(theorem=name):
                self.assertRegex(text, r'#check \(@' + re.escape(name) + r'\s*:')
                self.assertIn('#guard_standard_axioms ' + name, text)
                self.assertIn('#print axioms ' + name, text)
        whole = (audit.ROOT / 'audits/All.lean').read_text()
        for name in ('indexed_lower_bound', 'indexed_weak_lower_bound'):
            self.assertIn('#check (@ProjectiveLinkBounds.' + name + ' :', whole)
            self.assertIn('#guard_standard_axioms ' + PREFIX + '.' + name, whole)
            self.assertIn('#print axioms ' + PREFIX + '.' + name, whole)

    def test_separate_weak_proof_and_actual_occurrence_prerequisites(self):
        closures = audit.check_sources()
        weak = audit.closure(PREFIX + '.Weak')
        self.assertNotIn(audit.source(PREFIX + '.Deletion'), weak)
        deletion = audit.closure(PREFIX + '.Deletion')
        for part in ('Parity', 'Completion', 'Weak', 'Bounds'):
            self.assertNotIn(audit.source(PREFIX + '.' + part), deletion)
        new = {audit.source(module) for module in audit.PROJECTIVE_LINK_IMPORTS}
        for key, paths in closures.items():
            if key != KEY:
                self.assertFalse(paths & new, key)
        for module in ('ExactDesign.Counting', 'Multicover.Family', 'Equality.FiniteSum'):
            self.assertIn(audit.source('CoveringDesigns.' + module), closures[KEY])

    def test_forbidden_imports_are_rejected(self):
        root = memory_tree(source_headers(whole=True))
        with patch.object(audit, 'ROOT', root / 'lean'):
            for module, dependency, diagnostic in (
                ('C14_5_3.Examples', 'ProjectiveLinkBounds', 'Established component'),
                ('ProjectiveLinkBounds.Weak', 'ProjectiveLinkBounds.Deletion', 'Projective-link'),
                ('ProjectiveLinkBounds.Deletion', 'ProjectiveLinkBounds.Parity', 'Projective-link'),
                ('ProjectiveLinkBounds.Incidence', 'QuadrupleAssembly.Counting', 'Projective-link'),
                ('ProjectiveLinkBounds.Bounds', 'C14_5_3.Examples', 'Projective-link')):
                with self.subTest(module=module, dependency=dependency):
                    path = audit.source('CoveringDesigns.' + module)
                    original = path.read_text()
                    path.write_text(original + 'import CoveringDesigns.' + dependency + '\n')
                    try:
                        with self.assertRaisesRegex(AssertionError, diagnostic):
                            audit.check_sources()
                    finally:
                        path.write_text(original)

    def test_every_registered_axiom_result_is_required(self):
        info = audit.COMPONENTS[KEY]
        names = set(info['theorems'] + info['milestones'] + [audit.explicit_theorem(KEY)])
        lines = {n: "'" + n + "' depends on axioms: [propext, Classical.choice, Quot.sound]"
                 for n in names}
        audit.component_axioms(KEY, '\n'.join(lines.values()))
        for name in names:
            with self.subTest(missing=name), self.assertRaisesRegex(AssertionError, 'missing'):
                audit.component_axioms(KEY, '\n'.join(v for n, v in lines.items() if n != name))
        for name in (audit.principal_theorem(KEY), audit.explicit_theorem(KEY)):
            for replacement in ('propext, Classical.choice',
                                'propext, Classical.choice, Quot.sound, invented'):
                broken = dict(lines)
                broken[name] = "'" + name + "' depends on axioms: [" + replacement + ']'
                with self.subTest(theorem=name, axioms=replacement), self.assertRaises(AssertionError):
                    audit.component_axioms(KEY, '\n'.join(broken.values()))

    def test_focused_plan_builds_all_prerequisites_before_the_audit(self):
        plan = audit.verification_plan([KEY], 16384)
        names = list(plan)
        for path in audit.closure(PREFIX):
            name = 'build-' + str(path.relative_to(audit.ROOT)).removesuffix('.lean').replace('/', '.')
            self.assertIn(name, names)
            self.assertLess(names.index(name), names.index(audit.audit_name(KEY)))
        # Audit-only imports must also compile on a clean checkout.
        for entry in audit.project_imports(audit.audit_source(KEY).read_text()):
            for module in audit.module_order([entry]):
                name = 'build-' + module
                self.assertIn(name, names)
                self.assertLess(names.index(name), names.index(audit.audit_name(KEY)))
        self.assertEqual(len(names), len(set(names)))
        self.assertNotIn('build-CoveringDesigns.C14_5_3.Examples', names)


if __name__ == '__main__':
    unittest.main()
