"""Independent preserved witness and lift-inventory checks; no proof premises."""
from compression import zstd
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
import re
import sys

RETAINED = Path('data/pair-family/extensions')
WITNESSES = ((65, 13, 'Perona', 'Flavio Perona', '2011-05-21 03:32:48'),
             (95, 19, 'DeHeerMuir', 'Jan de Heer and Steve Muir', '2011-03-16 12:50:04'))


def check(data_only=False):
    provenance = json.loads((RETAINED / 'historical-provenance.json').read_text())
    reports = []
    for v, k, module, credit, date in WITNESSES:
        data = json.loads((RETAINED / f'witnesses/{v}-{k}-2.json').read_text())
        p = next(p for p in provenance['witnesses'] if p['parameters'] == [v, k, 2])
        assert [data[x] for x in ('v', 'k', 't')] == [v, k, 2]
        assert data['credit'] == credit and data['contribution_date'] == date
        assert data['licence'] == p['licence'] == 'CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository.'
        blocks = data['blocks']
        assert len(blocks) == 31
        assert all(len(b) == len(set(b)) == k for b in blocks)
        assert all(type(x) is int and 1 <= x <= v for b in blocks for x in b)
        assert len({frozenset(b) for b in blocks}) == 31
        assert {pair for b in blocks for pair in combinations(sorted(b), 2)} == set(combinations(range(1, v+1), 2))
        frame = (RETAINED / f'inputs/{v}-{k}-2.blocks.zst').read_bytes()
        raw = zstd.decompress(frame)
        assert len(frame) == p['compressed_bytes'] and sha256(frame).hexdigest() == p['compressed_sha256']
        assert len(raw) == p['raw_bytes'] and sha256(raw).hexdigest() == p['raw_sha256'] == data['original_raw_sha256']
        assert raw == bytes(x for b in blocks for x in b), 'archive/JSON ordered correspondence'
        if not data_only:
            text = Path(f'lean/CoveringDesigns/Qk_K_2/{module}.lean').read_text()
            text = text.split('def blocks :', 1)[1].split('/-- Distinctness', 1)[0]
            rows = [[int(x) for x in re.findall(r'\d+', b)] for b in re.findall(r'\{([^{}]+)\}', text)]
            assert rows == [[x-1 for x in b] for b in blocks], 'Lean ordered transcription'
        reports.append({'parameters': [v, k, 2], 'blocks': 31, 'pairs': v*(v-1)//2,
                        'credit': credit, 'raw_sha256': p['raw_sha256'], 'lean_correspondence': not data_only})
    inventory = json.loads((RETAINED / 'lift-inventory.json').read_text())
    snapshot = (RETAINED / 'inputs/coverdata.json').read_bytes()
    assert sha256(snapshot).hexdigest() == '0984bb8b4c89fe07268569b9814794e3c8852302d075f0794140f202e83d7fef'
    catalogue = json.loads(snapshot)
    assert len(inventory['rows']) == 59
    compared = [r for r in inventory['rows'] if r['catalogue_available']]
    assert len(compared) == 53
    seen = set()
    for r in inventory['rows']:
        v, k, t = r['seed']
        assert v == 4*k and t == 2 and k in (9,10,11,13,14,15,17,18,19,21,22,23)
        b = 21
        ceilings = []
        for step in r['chain']:
            v, k, t = v+1, k+1, t+1
            n = v*b
            value = (n+k-1)//k
            assert step == dict(denominator=k, derived=value, input_lower=b, numerator=n,
                                parameters=[v,k,t], quotient=n//k, remainder=n%k)
            assert k*(value-1) < n <= k*value
            b = value
            ceilings.append(b)
        assert r['parameters'] == [v,k,t] and r['derived'] == b and r['ceilings'] == ceilings
        assert (v,k,t) not in seen and v < 100 and k < 25 and 3 <= t <= 8
        seen.add((v,k,t))
        if r['catalogue_available']:
            assert r['lower'] < b < r['upper']
            key = f'C({v},{k},{t})'
            entry = catalogue[key]
            assert int(entry['low_bd']) == r['lower'] and int(entry['size']) == r['upper']
        else:
            assert f'C({v},{k},{t})' not in catalogue
    expected = {(4*k+j,k+j,2+j) for k in (9,10,11,13,14,15,17,18,19,21,22,23)
                for j in range(1,7) if 4*k+j < 100 and k+j < 25}
    assert seen == expected
    if not data_only:
        source = Path('lean/CoveringDesigns/Qk_K_2/Lifts.lean').read_text()
        names = re.findall(r'^theorem lower_bound_(\d+)_(\d+)_(\d+) ', source, re.M)
        assert {tuple(map(int, row)) for row in names} == {tuple(r['parameters']) for r in compared}
        for r in compared:
            v,k,t = r['parameters']; seed = r['seed'][1]; j = t-2; b = r['derived']
            pattern = (rf'theorem lower_bound_{v}_{k}_{t} .*?Fintype.card α = {v}\) '
                       rf'\(hC : IsCover C {k} {t}\) : {b} ≤ C.card := by\n'
                       rf'  have h := lifted_lower_bound {seed} \(by decide\) \(by decide\) {j} hv hC')
            assert re.search(pattern, source, re.S), f'Lift contract/seed mismatch: {v,k,t}'
        for r in inventory['rows']:
            v,k,t=r['parameters']; b=r['derived']
            assert f'Multicover.bound 21 {v} {k} {t-2} = {b}' in source
        table = Path('coverings/qk-k-2/lifting.md').read_text().split('## Six unavailable comparisons')[0]
        expected_rows = ['| '+','.join(map(str,r['seed']))+' | '+','.join(map(str,r['parameters']))+
                         f" | {r['lower']} | {r['derived']} | {r['upper']} | "+
                         ', '.join(map(str,r['ceilings']))+' |' for r in compared]
        actual_rows = [line for line in table.splitlines() if re.match(r'^\| \d', line)]
        assert actual_rows == expected_rows, 'Readable table correspondence'
    return {'witnesses': reports, 'descendants': 59, 'matched_comparisons': 53,
            'unavailable_comparisons': 6, 'all_intermediate_ceilings_checked': True}


if __name__ == '__main__':
    print(json.dumps(check('--data-only' in sys.argv), indent=2))
