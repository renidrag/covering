"""Exact correspondence for the reviewed 78 direct numerical consumers.

The generated Lean text proves every assertion. This checker is data hygiene,
not a certificate accepted by Lean. Historical-dependent rows are excluded.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / 'data/pair-family/consequences/proposed-additions.json'
SOURCE = ROOT / 'lean/CoveringDesigns/PairConsequences/Numerical.lean'
INVENTORY_SHA = '4d609517fd2fc216af82afb20379f2642930be25db9cc92500a9fee85d216435'

def accepted_rows():
    assert sha256(INVENTORY.read_bytes()).hexdigest() == INVENTORY_SHA
    all_rows = json.loads(INVENTORY.read_text())
    rows = sorted((r for r in all_rows if r['dependency_class'] == 'batch'),
                  key=lambda r: (r['parameters'][2],r['parameters'][0],r['parameters'][1]))
    assert len(rows) == 78 and len(all_rows) - len(rows) == 14
    assert Counter(r['comparison_status'] for r in rows) == {
        'refreshed LJCR':50,'retained cvkt':5,'missing':23}
    old = json.loads((ROOT/'data/pair-family/extensions/lift-inventory.json').read_text())
    old_params = {tuple(r['parameters']) for r in old['rows']}
    assert len(old_params) == 59
    seen = set()
    for r in rows:
        params = tuple(r['parameters'])
        assert params not in old_params and params not in seen
        seen.add(params)
        seed = r['derivation'][0]
        v,k,t = seed['parameters']; b=seed['lower']
        assert t==2 and seed['op']=='batch seed'
        assert (v,k,b) in {(42,7,43),(55,11,31),(56,8,57),(65,13,31),(70,14,31),
            (78,13,43),(80,16,31),(84,14,43),(85,17,31),(90,10,91),
            (90,15,43),(95,19,31),(96,16,43)}
        for s in r['derivation'][1:]:
            v,k,t=v+1,k+1,t+1; n=v*b; b=s['lower']
            assert s['op']=='Schonheim lift' and s['parameters']==[v,k,t]
            assert (b-1)*k<n<=b*k and (s['numerator'],s['denominator'])==(n,k)
            assert divmod(n,k)==(s['quotient'],s['remainder'])
        assert (v,k,t)==params and b==r['lower']
    return rows

def numerical_source():
    out = ['import CoveringDesigns.PairConsequences.Arithmetic',
           'import CoveringDesigns.Qk_K_2.NumericalLower',
           'import CoveringDesigns.LiftingComparison.Covering', '',
           '/-! The 78 reviewed direct bounds. Every lift uses the existing universal',
           'residual theorem and retains each ceiling. Comparison categories are dated',
           'metadata, not proof premises or historical novelty claims. -/',
           'namespace CoveringDesigns.PairConsequences', '']
    for r in accepted_rows():
        v,k,t=r['parameters']; b=r['lower']; j=t-2
        seed=r['derivation'][0]; sv,sk,_=seed['parameters']; sb=seed['lower']
        name=f'{v}_{k}_{t}'
        out += [f'-- {r["comparison_status"]}; comparison inputs retained 27 October 2026.',
          f'theorem indexed_lower_{name} {{I X : Type*}} [Fintype I]',
          f'    [Fintype X] [DecidableEq X] {{B : I → Finset X}}',
          f'    (hv : Fintype.card X = {v}) (hB : Multicover.IsCover B {k} {t} 1) :',
          f'    {b} ≤ Fintype.card I := by', '  classical']
        if j==0:
            out += ['  exact indexed_six (by decide) hv hB (by decide)']
        else:
            seed_call = (f'indexed_six (by decide) hn hD (by decide)' if sv==6*sk
                else f'Qk_K_2.indexed_lower_{sv}_{sk}_2 hn hD')
            out += [f'  have hs : Multicover.CoverLower ({v}-{j}) ({k}-{j}) ({t}-{j}) 1 {sb} := by',
                    '    intro Y J _ _ _ D hn hD', '    classical', f'    exact {seed_call}',
                    f'  have h := LiftingComparison.indexed_lower_bound (s := {j})',
                    '    (by decide) (by decide) (by decide) hs hv hB',
                    f'  have he : LiftingComparison.iterate {v} {k} {j} {sb} = {b} := by decide',
                    '  exact he ▸ h']
        out += ['',f'theorem lower_bound_{name} {{X : Type*}} [Fintype X] {{C : Family X}}',
                f'    (hv : Fintype.card X = {v}) (hC : IsCover C {k} {t}) : {b} ≤ C.card := by',
                '  classical',f'  simpa using indexed_lower_{name} hv ((Multicover.ofFamily_isCover_one C {k} {t}).mpr hC)','']
    return '\n'.join(out)+ '\nend CoveringDesigns.PairConsequences\n'

def check():
    rows=accepted_rows()
    assert SOURCE.read_text()==numerical_source(), 'Numerical contract/derivation correspondence changed'
    audit=(ROOT/'lean/audits/PairConsequences.lean').read_text()
    for r in rows:
        v,k,t=r['parameters']; b=r['lower']
        for prefix in ('lower_bound','indexed_lower'):
            name=f'CoveringDesigns.PairConsequences.{prefix}_{v}_{k}_{t}'
            assert f'#check (@{name} :' in audit, name
            assert f'#guard_standard_axioms {name}' in audit, name
            assert f'#print axioms {name}' in audit, name
        pattern=(rf'#check \(@CoveringDesigns.PairConsequences.lower_bound_{v}_{k}_{t} :'
                 rf'.*?Fintype.card X = {v}\).*?IsCover C {k} {t}\).*?{b} ≤ C.card\)')
        assert re.search(pattern,audit,re.S), f'Typed ordinary contract mismatch {v,k,t}'
    return {'direct':78,'refreshed_LJCR':50,'retained_cvkt':5,'missing_comparison':23,
            'historical_excluded':14,'previous_lifts_excluded':59,'kernel_declarations':156}

if __name__=='__main__':
    import sys
    if '--write' in sys.argv:
        SOURCE.write_text(numerical_source())
        print('Wrote 78 ordinary and 78 indexed numerical consumers.')
    else:
        print(json.dumps(check(),indent=2))
