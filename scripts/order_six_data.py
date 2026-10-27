"""Exact retained fourteen-row correspondence; no mathematical certificate.

The Lean consumers use the existing universal lifting theorem. Comparisons
remain dated metadata. This checker never changes the retained inventories.
"""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
INVENTORY = ROOT / 'data/pair-family/consequences/proposed-additions.json'
SOURCE = ROOT / 'lean/CoveringDesigns/C6k_K_2/Numerical.lean'
INVENTORY_SHA = '4d609517fd2fc216af82afb20379f2642930be25db9cc92500a9fee85d216435'

def recovered_rows():
    assert sha256(INVENTORY.read_bytes()).hexdigest() == INVENTORY_SHA
    inventory = json.loads(INVENTORY.read_text())
    rows = sorted((r for r in inventory if r['dependency_class'] == 'BR1949'),
                  key=lambda r: (r['parameters'][2], r['parameters'][0]))
    expected = {(v+s, k+s, 2+s): b for v, k, bounds in (
        (36, 6, (43, 228, 1083, 4693, 18772, 69969, 244892)),
        (72, 12, (43, 242, 1280, 6400, 30400, 137695, 596679)))
        for s, b in enumerate(bounds)}
    assert len(rows) == 14
    assert {tuple(r['parameters']): r['lower'] for r in rows} == expected
    assert Counter(r['comparison_status'] for r in rows) == {
        'refreshed LJCR': 9, 'retained cvkt': 2, 'missing': 3}
    direct = {tuple(r['parameters']) for r in inventory if r['dependency_class'] == 'batch'}
    old = json.loads((ROOT / 'data/pair-family/extensions/lift-inventory.json').read_text())
    old_params = {tuple(r['parameters']) for r in old['rows']}
    assert len(direct) == 78 and len(old_params) == 59
    assert not set(expected) & (direct | old_params)
    # Also exclude already named ordinary or indexed lower-bound declarations.
    old_names = set()
    for path in (ROOT / 'lean/CoveringDesigns').rglob('*.lean'):
        if path.is_relative_to(SOURCE.parent):
            continue
        old_names.update(tuple(map(int, m)) for m in re.findall(
            r'^theorem (?:lower_bound|indexed_lower)_(\d+)_(\d+)_(\d+)\b', path.read_text(), re.M))
    assert not set(expected) & old_names
    for row in rows:
        seed = row['derivation'][0]
        v, k, t = seed['parameters']; b = seed['lower']
        assert (v, k, t, b) in ((36, 6, 2, 43), (72, 12, 2, 43))
        for step in row['derivation'][1:]:
            v, k, t = v+1, k+1, t+1
            numerator = v*b
            b = step['lower']
            assert step['op'] == 'Schonheim lift' and step['parameters'] == [v, k, t]
            assert (b-1)*k < numerator <= b*k
            assert (step['numerator'], step['denominator']) == (numerator, k)
            assert divmod(numerator, k) == (step['quotient'], step['remainder'])
        assert (v, k, t) == tuple(row['parameters']) and b == row['lower']
        assert not row['exact']
        assert row['upper_proved'] is None or row['upper_proved'] > row['lower']
    return rows

def inventory_report():
    rows = recovered_rows()
    return {'rows': 14, 'pair_seeds': 2, 'positive_step_lifts': 12,
            'refreshed_LJCR': 9, 'retained_cvkt': 2, 'missing_comparison': 3,
            'deduplicated_direct_rows': 78, 'deduplicated_previous_lifts': 59,
            'existing_named_bounds_disjoint': True, 'every_intermediate_ceiling_checked': True,
            'parameters_and_bounds': [[*r['parameters'], r['lower']] for r in rows]}

def numerical_source():
    out = ['import CoveringDesigns.C6k_K_2.LowerBound',
           'import CoveringDesigns.LiftingComparison.Covering', '',
           '/-! The fourteen retained order-six consequences: two seeds and twelve lifts.',
           'Every intermediate ceiling is retained by the existing lifting recurrence. -/',
           'namespace CoveringDesigns.C6k_K_2', '']
    for row in recovered_rows():
        v, k, t = row['parameters']; b = row['lower']; s = t-2
        name = f'{v}_{k}_{t}'
        out += [f'-- {row["comparison_status"]}; comparison inputs retained 27 October 2026.',
                f'-- {row["concise_derivation"]}',
                f'theorem indexed_lower_{name} {{I X : Type*}} [Fintype I]',
                '    [Fintype X] [DecidableEq X] {B : I → Finset X}',
                f'    (hv : Fintype.card X = {v}) (hB : Multicover.IsCover B {k} {t} 1) :',
                f'    {b} ≤ Fintype.card I := by', '  classical']
        if s == 0:
            out += ['  exact indexed_lower_bound (by decide) hv hB']
        else:
            out += [f'  have hs : Multicover.CoverLower ({v}-{s}) ({k}-{s}) ({t}-{s}) 1 43 := by',
                    '    intro Y J _ _ _ D hn hD', '    classical',
                    '    exact indexed_lower_bound (by decide) hn hD',
                    f'  have h := LiftingComparison.indexed_lower_bound (s := {s})',
                    '    (by decide) (by decide) (by decide) hs hv hB',
                    f'  have he : LiftingComparison.iterate {v} {k} {s} 43 = {b} := by decide',
                    '  exact he ▸ h']
        out += ['', f'theorem lower_bound_{name} {{X : Type*}} [Fintype X] {{C : Family X}}',
                f'    (hv : Fintype.card X = {v}) (hC : IsCover C {k} {t}) : {b} ≤ C.card := by',
                '  classical',
                f'  simpa using indexed_lower_{name} hv ((Multicover.ofFamily_isCover_one C {k} {t}).mpr hC)', '']
    return '\n'.join(out) + '\nend CoveringDesigns.C6k_K_2\n'

def check():
    assert SOURCE.read_text() == numerical_source(), 'Order-six numerical correspondence changed'
    audit = (ROOT / 'lean/audits/C6k_K_2.lean').read_text()
    for row in recovered_rows():
        v, k, t = row['parameters']; b = row['lower']
        for prefix, conclusion in (('lower_bound', f'{b} ≤ C.card'),
                                   ('indexed_lower', f'{b} ≤ Fintype.card I')):
            name = f'CoveringDesigns.C6k_K_2.{prefix}_{v}_{k}_{t}'
            for command in ('#check (@', '#guard_standard_axioms ', '#print axioms '):
                assert command + name in audit, name
            cover = f'IsCover C {k} {t}' if prefix == 'lower_bound' else f'Multicover.IsCover B {k} {t} 1'
            pattern = re.escape(f'#check (@{name} :') + r'.*?' + re.escape(f'Fintype.card X = {v}')
            pattern += r'.*?' + re.escape(cover) + r'.*?' + re.escape(conclusion + ')')
            assert re.search(pattern, audit, re.S), f'Typed contract mismatch: {name}'
    return inventory_report() | {'kernel_declarations': 28}

if __name__ == '__main__':
    import sys
    if '--inventory' in sys.argv:
        print(json.dumps(inventory_report(), indent=2))
    elif '--write' in sys.argv:
        SOURCE.write_text(numerical_source())
        print('Wrote fourteen ordinary and fourteen indexed consumers.')
    else:
        print(json.dumps(check(), indent=2))
