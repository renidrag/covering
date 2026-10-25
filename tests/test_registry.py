"""Exhaustive registry checks with independent graph/registration expectations."""
import re
import unittest
from unittest.mock import patch

from workflow_fixtures import ROOT, audit, header_graph, memory_tree, reachable, source_headers
import workflow
from covering_cli import parser_for_cli


class Registry(unittest.TestCase):
    def setUp(self):
        self.headers = source_headers(whole=True)
        self.graph = header_graph(self.headers)
        self.root = memory_tree(self.headers)
        override = patch.object(audit, 'ROOT', self.root / 'lean')
        override.start()
        self.addCleanup(override.stop)

    def test_every_registered_plan_has_exact_closure_and_dependency_order(self):
        entries = {info['entry'] for info in audit.COMPONENTS.values()}
        self.assertLessEqual(set(self.graph['CoveringDesigns']), entries)
        self.assertLessEqual(entries, reachable(self.graph, 'CoveringDesigns'))
        self.assertEqual(workflow.TARGETS, ('all', *audit.COMPONENTS))
        parser = parser_for_cli()
        summaries, audits = set(), set()
        for key, info in audit.COMPONENTS.items():
            with self.subTest(component=key):
                for action in ('plan', 'verify', 'audit', 'status'):
                    self.assertEqual(parser.parse_args([action, key]).target, key)
                steps = workflow.plan_for(key, workflow.DEFAULT_LIMITS)
                builds = [s for s in steps if s['kind'] == 'build']
                modules = [s['name'].removeprefix('build-') for s in builds]
                roots = [info['entry'], *info.get('verification_entries', [])]
                expected = set().union(*(reachable(self.graph, root) for root in roots))
                self.assertEqual(set(modules), expected)
                self.assertEqual(len(modules), len(expected))
                positions = {module: index for index, module in enumerate(modules)}
                for module in expected:
                    for dependency in self.graph[module]:
                        self.assertLess(positions[dependency], positions[module])
                if not info.get('verification_entries'):
                    self.assertEqual(modules[-1], info['entry'])
                expected_name = info.get('audit_name', 'c' + key.split('-')[0] + '-audit')
                expected_file = info.get('audit_file', 'C' + key.replace('-', '_') + '.lean')
                self.assertEqual(steps[-1]['name'], expected_name)
                self.assertEqual(steps[-1]['command'][-1], 'lean/audits/' + expected_file)
                self.assertEqual(len(steps), len(builds) + 1)
                self.assertNotIn(expected_name, audits)
                audits.add(expected_name)
                summary = workflow.summary_path(key)
                expected_summary = ('results/c13-structural-verification.json' if key == '13-7-4'
                                    else info.get('summary_path', 'results/c' + key.split('-')[0] + '-verification.json'))
                self.assertEqual(str(summary), expected_summary)
                self.assertNotIn(summary, summaries)
                summaries.add(summary)

    def test_real_graph_passes_all_source_boundaries(self):
        checked = audit.check_sources()
        self.assertEqual(set(checked), set(audit.COMPONENTS))
        for key, info in audit.COMPONENTS.items():
            with self.subTest(component=key):
                expected = {'lean/' + m.replace('.', '/') + '.lean'
                            for m in reachable(self.graph, info['entry'])}
                self.assertEqual(set(map(str, checked[key])), expected)

    def test_dependency_cycles_and_missing_imports_fail_closed(self):
        first = self.root / 'lean/CoveringDesigns/ProbeA.lean'
        second = self.root / 'lean/CoveringDesigns/ProbeB.lean'
        first.write_text('import CoveringDesigns.ProbeB\n')
        with self.assertRaisesRegex(AssertionError, 'Missing local import'):
            audit.module_order(['CoveringDesigns.ProbeA'])
        second.write_text('import CoveringDesigns.ProbeA\n')
        with self.assertRaisesRegex(AssertionError, 'Import cycle'):
            audit.module_order(['CoveringDesigns.ProbeA'])

    def test_separate_source_checks_observe_changed_imports(self):
        audit.check_sources()
        path = self.root / 'lean/CoveringDesigns/C11_5_2.lean'
        original = path.read_text()
        path.write_text(original + 'import CoveringDesigns.C12_6_3\n')
        with self.assertRaises((AssertionError, ValueError)):
            audit.check_sources()
        path.write_text(original)
        self.assertEqual(set(audit.check_sources()), set(audit.COMPONENTS))

    def test_every_declared_independent_component_is_rejected(self):
        # This test isolates the boundary decision from graph traversal. Supply
        # fresh closure inputs calculated by the independent work-list oracle.
        # The tests above check the production walker against that oracle for
        # every real component; named transitive and CLI tests use it unchanged.
        # No closure cache, disk fixture, or subprocess is needed per forbidden
        # pair. A new graph is supplied for every case, with no retained results.
        paths = {module: self.root / ('lean/' + module.replace('.', '/') + '.lean')
                 for module in self.graph}
        for key, info in audit.COMPONENTS.items():
            path = self.root / ('lean/' + info['entry'].replace('.', '/') + '.lean')
            original = path.read_text()
            for other in info['independent_of']:
                if other in audit.PUBLICATION_BOUNDARIES:
                    forbidden = [audit.PUBLICATION_BOUNDARIES[other]]
                else:
                    # C13's historical metadata also names a module boundary,
                    # rather than another registered component. Exercise it too.
                    self.assertEqual(other, 'GPPT catalogue and completion enumeration')
                    forbidden = ['CoveringDesigns.C12_6_3.' + part for part in (
                        'Catalogue', 'CatalogueBridge', 'Classification',
                        'Structural.CompletionEncoding', 'Structural.CompletionData',
                        'Structural.CompletionSupport', 'Structural.CompletionChecks',
                        'Structural.Completions')]
                for module in forbidden:
                    with self.subTest(component=key, forbidden=module):
                        target = self.root / ('lean/' + module.replace('.', '/') + '.lean')
                        created = not target.is_file()
                        if created:
                            target.write_text('')
                        paths[module] = target
                        graph = {**self.graph, module: self.graph.get(module, ())}
                        graph[info['entry']] = (*self.graph[info['entry']], module)
                        path.write_text(original + 'import ' + module + '\n')
                        try:
                            def supplied_closure(_graph, entry):
                                return {paths[m] for m in reachable(graph, entry)}

                            with patch.object(audit.SourceGraph, 'closure', supplied_closure), \
                                    self.assertRaises((AssertionError, ValueError)):
                                audit.check_sources()
                        finally:
                            path.write_text(original)
                            if created:
                                target.unlink()

    def test_audit_declarations_cover_the_registry_and_explicit_contracts(self):
        # This is a source coverage check. Only Lean verifies the full types.
        # Bare or namespace-relative names in older audits resolve by suffix;
        # the independent Lean record still checks elaboration and ambiguity.
        for key, info in audit.COMPONENTS.items():
            path = ROOT / str(audit.audit_source(key))
            content = path.read_text()
            printed = set(re.findall(r'^#print axioms\s+(\S+)', content, re.M))
            required = info['theorems'] + info['milestones'] + [audit.explicit_theorem(key)]
            with self.subTest(component=key):
                self.assertIn(info['entry'], audit.project_imports(content))
                for name in required:
                    self.assertTrue(any(name == p or name.endswith('.' + p) for p in printed), name)
                explicit = audit.explicit_theorem(key).split('.')[-1]
                declared = re.search(r'(?s)theorem\s+' + re.escape(explicit) + r'\b.*?:.*?:=', content)
                typed_check = re.search(r'#check\s*\(\s*@?(?:[\w.]+\.)?' + re.escape(explicit) + r'\s*:', content)
                self.assertTrue(declared or typed_check, f'{key}: missing explicit typed contract')
                self.assertTrue('#check' in content or '#print ' in content)


    def test_c20_public_contracts_are_exhaustive(self):
        info = audit.COMPONENTS['20-11-3']
        # Own only modules actually imported by the original component;
        # future reusable BoundaryRank files have their own contract audits.
        modules = reachable(self.graph, info['entry'])
        paths = [ROOT / 'lean' / (module.replace('.', '/') + '.lean')
                 for module in modules if module == info['entry'] or
                 module.startswith(('CoveringDesigns.C20_11_3.', 'CoveringDesigns.BoundaryRank.'))]
        declarations = set()
        for path in paths:
            source = path.read_text()
            namespace = re.search(r'^namespace\s+(\S+)', source, re.M).group(1)
            declarations.update(namespace + '.' + name for name in
                re.findall(r'^(?:@\[[^\]]+\]\s*)?theorem\s+(\w+)', source, re.M))
        self.assertEqual(set(info['theorems']), declarations)
        content = (ROOT / str(audit.audit_source('20-11-3'))).read_text()
        for name in declarations:
            self.assertRegex(content, r'#check\s*\(\s*@' + re.escape(name) + r'\s*:')

    def test_two_k_public_contracts_are_exhaustive(self):
        info = audit.COMPONENTS['two-k-minus-two']
        paths = [ROOT / 'lean/CoveringDesigns/TwoKMinusTwo.lean']
        paths.extend((ROOT / 'lean/CoveringDesigns/TwoKMinusTwo').glob('*.lean'))
        declarations = {info['entry'] + '.' + name for path in paths for name in
                        re.findall(r'^theorem\s+(\w+)', path.read_text(), re.M)}
        self.assertEqual(set(info['theorems']), declarations)
        content = (ROOT / str(audit.audit_source('two-k-minus-two'))).read_text()
        for name in declarations:
            self.assertRegex(content, r'#check\s*\(\s*@' + re.escape(name) + r'\s*:')



    def test_two_k_equality_public_contracts_are_exhaustive(self):
        info = audit.COMPONENTS['two-k-minus-two-equality']
        paths = [ROOT / 'lean/CoveringDesigns/TwoKMinusTwoEquality.lean',
                 ROOT / 'lean/CoveringDesigns/BoundaryRank/Equality.lean']
        paths.extend((ROOT / 'lean/CoveringDesigns/TwoKMinusTwoEquality').glob('*.lean'))
        declarations = set()
        for path in paths:
            source = path.read_text()
            namespace = re.search(r'^namespace\s+(\S+)', source, re.M).group(1)
            declarations.update(namespace + '.' + name for name in
                                re.findall(r'^theorem\s+(\w+)', source, re.M))
        self.assertEqual(set(info['theorems']), declarations)
        content = (ROOT / str(audit.audit_source('two-k-minus-two-equality'))).read_text()
        for name in declarations:
            self.assertRegex(content, r'#check\s*\(\s*@' + re.escape(name) + r'\s*:')


    def test_offset_public_contracts_are_exhaustive(self):
        info = audit.COMPONENTS['two-k-minus-c']
        declarations = set()
        for path in (ROOT / 'lean/CoveringDesigns/TwoKMinusC').glob('*.lean'):
            source = path.read_text()
            namespace = re.search(r'^namespace\s+(\S+)', source, re.M).group(1)
            declarations.update(namespace + '.' + name for name in
                                re.findall(r'^theorem\s+(\w+)', source, re.M))
        self.assertEqual(set(info['theorems']), declarations)
        content = (ROOT / str(audit.audit_source('two-k-minus-c'))).read_text()
        for name in declarations:
            self.assertRegex(content, r'#check\s*\(\s*@' + re.escape(name) + r'\s*:')



    def test_fixed_offset_public_contracts_are_exhaustive(self):
        info = audit.COMPONENTS['two-k-minus-c-general']
        paths = [ROOT / 'lean/CoveringDesigns/Weighted/PartitionedRank.lean']
        paths.extend((ROOT / 'lean/CoveringDesigns/TwoKMinusCGeneral').glob('*.lean'))
        declarations = set()
        for path in paths:
            source = path.read_text()
            namespace = re.search(r'^namespace\s+(\S+)', source, re.M).group(1)
            declarations.update(namespace + '.' + name for name in
                                re.findall(r'^theorem\s+(\w+)', source, re.M))
        self.assertEqual(set(info['theorems']), declarations)
        content = (ROOT / str(audit.audit_source('two-k-minus-c-general'))).read_text()
        for name in declarations:
            self.assertRegex(content, r'#check\s*\(\s*@' + re.escape(name) + r'\s*:')

if __name__ == '__main__':
    unittest.main()
