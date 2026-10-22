"""Controls for the external literal boundary; no mathematical proof claims."""
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

PATH=Path(__file__).resolve().parents[1]/'scripts/check_quadruple_data.py'
spec=importlib.util.spec_from_file_location('quadruple_boundary',PATH)
boundary=importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)


class QuadrupleBoundaryTests(unittest.TestCase):
    literal='def piece0 : List (Finset (Fin 13)) := [\n  {0,1,2,3}\n]\n\ntheorem marker : True := by trivial\n'

    def test_actual_projections_and_pinned_inputs(self):
        results=boundary.check()
        self.assertEqual(sum(r['points'] in [37,49,61,73,85,97] for r in results),6)

    def test_numeric_bounds_prevent_fin_wrapping(self):
        with self.assertRaises(AssertionError):
            boundary.parse_literals(self.literal.replace('{0,1,2,3}','{13,1,2,3}'),13)

    def test_commented_declaration_is_not_data(self):
        for text in ['/- '+self.literal+' -/','/- outer /- nested -/ '+self.literal+' -/']:
            with self.assertRaises(AssertionError):boundary.parse_literals(text,13)

    def test_trailing_expression_is_rejected(self):
        for tail in [' ++ []',' |>.drop 1']:
            with self.assertRaises(AssertionError):
                boundary.parse_literals(self.literal.replace(']\n',']'+tail+'\n'),13)

    def test_deleted_duplicated_and_mutated_rows_fail(self):
        actual=[[0,1,2,3],[4,5,6,7]]
        for changed in [actual[:-1],actual+[actual[0]],[[0,1,2,4],actual[1]]]:
            with self.assertRaises(AssertionError):boundary.compare_rows(actual,changed,13)

    def test_reordering_is_lossless(self):
        boundary.compare_rows([[0,1,2,3],[4,5,6,7]],[[7,6,5,4],[3,2,1,0]],13)

    def test_join_cannot_omit_duplicate_or_hide_tail(self):
        parts=[self.literal.replace('piece0',f'piece{i}') for i in range(4)]
        joined='\n'.join(f'def file{k} : List (Finset (Fin 13)) := [piece{i}].flatten' for i,k in enumerate('ABCD'))
        joined+='\ndef rows : List (Finset (Fin 13)) := fileA ++ fileB ++ fileC ++ fileD\ndef blocks : Family (Fin 13) := rows.toFinset\n'
        self.assertEqual(len(boundary.witness_projection(parts,joined,13)),4)
        for bad in [joined.replace('[piece3]','[piece2]'),joined.replace('[piece3]','[]'),
                    joined.replace('rows.toFinset','rows.toFinset.erase {0,1,2,3}'),
                    '/- '+joined+' -/']:
            with self.assertRaises((AssertionError,KeyError)):
                boundary.witness_projection(parts,bad,13)

    def test_base_family_cannot_erase_or_replace_rows(self):
        text=self.literal.replace('piece0','rows').split('theorem marker')[0]
        text+='def blocks : Family (Fin 13) := rows.toFinset\n'
        self.assertEqual(boundary.base_projection(text,13),[[0,1,2,3]])
        for bad in [text.replace('rows.toFinset','rows.toFinset.erase {0,1,2,3}'),
                    text.replace('rows.toFinset','∅'),text.replace('Family (Fin 13)','Family (Fin 14)')]:
            with self.assertRaises(AssertionError):boundary.base_projection(bad,13)

    def test_historical_cover_controls_and_valid_relabelling(self):
        rows=json.loads((boundary.ROOT/'data/quadruple-assembly/blocks-25-4-3-600.json').read_text())['blocks']
        report=boundary.check_cover(rows,25,600)
        self.assertEqual(report['covered_triples'],2300)
        self.assertEqual(report['triple_multiplicity_histogram'],{1:2200,2:100})
        invalid=[rows[:-1],rows[:-1]+[rows[0]],[[25,*rows[0][1:]],*rows[1:]],
                 [[True,*rows[0][1:]],*rows[1:]]]
        for changed in invalid:
            with self.assertRaises(AssertionError):boundary.check_cover(changed,25,600)
        # A valid new quadruple, preserving count/distinctness but leaving a hole.
        old={tuple(row) for row in rows}
        replacement=next(list(row) for row in combinations(range(25),4) if row not in old)
        changed=[replacement,*rows[1:]]
        boundary.compare_rows(changed,changed,25,600)
        with self.assertRaisesRegex(AssertionError,'uncovered triples'):
            boundary.check_cover(changed,25,600)
        relabelled=[[24-x for x in row] for row in rows]
        self.assertEqual(boundary.check_cover(relabelled,25,600)['covered_triples'],2300)

    def test_original_artifact_and_normalization_controls(self):
        manifest=json.loads(boundary.MANIFEST.read_text())
        item=manifest['historical_witnesses'][0]
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            for key in ('record','source','original'):
                dest=root/item[key];dest.parent.mkdir(parents=True,exist_ok=True)
                dest.write_bytes((boundary.ROOT/item[key]).read_bytes())
            boundary.check_historical_witness(root,item)
            path=root/item['source'];original=path.read_bytes();data=json.loads(original)
            data['blocks'][0][0]=1
            path.write_text(json.dumps(data))
            with self.assertRaises(AssertionError):boundary.check_historical_witness(root,item)
            path.write_bytes(original)
            data=json.loads(original);data['t']=True;path.write_text(json.dumps(data))
            with self.assertRaises(AssertionError):boundary.check_historical_witness(root,item)
            path.write_bytes(original)
            raw=root/item['original'];data=bytearray(raw.read_bytes());data[0]^=1;raw.write_bytes(data)
            with self.assertRaisesRegex(AssertionError,'compressed digest'):
                boundary.check_historical_witness(root,item)

    def test_missing_zstd_fails_before_reading_or_skipping_the_original(self):
        with patch.dict('sys.modules', {'compression.zstd': None}):
            with self.assertRaisesRegex(RuntimeError, 'cannot be skipped'):
                boundary.check_historical_witness(Path('/unused'), {})

    def test_relocated_inputs_are_pinned_and_cannot_escape_the_package(self):
        spec=importlib.util.spec_from_file_location('quadruple_generator',PATH.with_name('quadruple_data.py'))
        generator=importlib.util.module_from_spec(spec);spec.loader.exec_module(generator)
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);manifest=root/'coverings/12u-plus-1-4-3/inputs.json'
            manifest.parent.mkdir(parents=True)
            source='research/retained.json';local='data/local.json'
            data={'inputs':[{'path':local}], 'input_locations':{source:local}}
            manifest.write_text(json.dumps(data))
            with patch.object(generator,'ROOT',root):
                self.assertEqual(generator.input_file(root/source),root/local)
                data['input_locations'][source]='absent.json';manifest.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError,'Unpinned'):generator.input_file(root/source)
                data={'inputs':[{'path':'../outside'}],'input_locations':{source:'../outside'}}
                manifest.write_text(json.dumps(data))
                with self.assertRaisesRegex(ValueError,'escapes'):generator.input_file(root/source)


if __name__=='__main__':unittest.main()
