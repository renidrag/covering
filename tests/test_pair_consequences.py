"""Integration and negative controls; mathematical evidence comes from Lean."""
from pathlib import Path
import re
import unittest
from unittest.mock import patch

from workflow_fixtures import ROOT, audit
import workflow
from pair_consequences_registration import PC_IMPORTS, PC_THEOREMS
from pair_consequence_data import check


class PairConsequences(unittest.TestCase):
    def test_established_components_remain_independent(self):
        graph=audit.SourceGraph()
        new={audit.source(m) for m in PC_IMPORTS}
        for key,info in audit.COMPONENTS.items():
            if key not in ('pair-consequences', '6k-k-2'):
                self.assertFalse(graph.closure(info['entry']) & new,key)

    def test_all_public_contracts_are_typed_and_axiom_guarded(self):
        names=set()
        for module in PC_IMPORTS:
            text=audit.source(module).read_text()
            names.update('CoveringDesigns.PairConsequences.'+name for name in re.findall(
                r'^(?:@\[simp\] )?(?:noncomputable )?(?:def|theorem) (\w+)',text,re.M))
        self.assertEqual(names,set(PC_THEOREMS))
        text=audit.audit_source('pair-consequences').read_text()
        for name in names:
            for prefix in ('#check (@','#guard_standard_axioms ','#print axioms '):
                self.assertIn(prefix+name,text)

    def test_plan_includes_all_consumers_and_audit(self):
        names={s['name'] for s in workflow.plan_for('pair-consequences',workflow.DEFAULT_LIMITS)}
        for part in ('Arithmetic','Equality','Primitive','Intervals','Replication','Numerical'):
            self.assertIn('build-CoveringDesigns.PairConsequences.'+part,names)
        self.assertIn('pair-consequences-audit',names)

    def test_numerical_correspondence_and_categories(self):
        report=check()
        self.assertEqual(report['direct'],78)
        self.assertEqual(report['kernel_declarations'],156)
        self.assertEqual(report['historical_excluded'],14)
        self.assertEqual(report['previous_lifts_excluded'],59)

    def test_rejects_changed_public_bound(self):
        original=Path.read_text
        def changed(path,*args,**kwargs):
            text=original(path,*args,**kwargs)
            if str(path).endswith('PairConsequences/Numerical.lean'):
                return text.replace(': 13215 ≤ C.card',': 13216 ≤ C.card',1)
            return text
        with patch.object(Path,'read_text',changed),self.assertRaisesRegex(AssertionError,'correspondence'):
            check()

    def test_rejects_missing_typed_contract(self):
        original=Path.read_text
        def changed(path,*args,**kwargs):
            text=original(path,*args,**kwargs)
            if str(path).endswith('audits/PairConsequences.lean'):
                return text.replace('#check (@CoveringDesigns.PairConsequences.lower_bound_99_23_6 :',
                                    '#check (@CoveringDesigns.PairConsequences.lower_bound_99_23_6_bad :',1)
            return text
        with patch.object(Path,'read_text',changed),self.assertRaises(AssertionError):
            check()


if __name__=='__main__':
    unittest.main()
