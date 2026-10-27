"""Independent retained-data and exact Lean correspondence check; no data writes."""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from compression import zstd
import json
import re

RETAINED = Path('data/pair-family/barker')


def check():
    path = RETAINED / 'witnesses/44-11-2.json'
    assert sha256(path.read_bytes()).hexdigest() == \
        '0ee62241734f735cecb28db28400dbf90ab9dc4a617a12b3587abca15dffeb4b', 'Barker retained JSON changed'
    data = json.loads(path.read_text())
    assert [data[x] for x in ('v', 'k', 't')] == [44, 11, 2]
    assert data['credit'] == 'Colin Barker'
    assert data['contribution_date'] == '2008-12-01 09:10:02'
    assert data['licence'] == 'CC BY 4.0; Daniel M. Gordon / La Jolla Covering Repository.'
    blocks = data['blocks']
    assert len(blocks) == 21
    assert all(len(b) == len(set(b)) == 11 for b in blocks)
    assert all(type(x) is int and 1 <= x <= 44 for b in blocks for x in b)
    assert len({frozenset(b) for b in blocks}) == 21
    assert {p for b in blocks for p in combinations(sorted(b), 2)} == set(combinations(range(1, 45), 2))
    frame = (RETAINED / 'inputs/C-44-11-2.blocks.zst').read_bytes()
    assert sha256(frame).hexdigest() == 'a97881d397f3396d29ae38c91dd8fb5735098fe836e6135305a74bf17972a914'
    raw = zstd.decompress(frame)
    assert raw == bytes(x for b in blocks for x in b), 'Barker archive/JSON correspondence'
    assert sha256(raw).hexdigest() == '523a8bdc8338e034c465532bd2207a644d8ae1131688bbcda465aa65d3a9a794'
    provenance = json.loads((RETAINED / 'provenance-44-11-2.json').read_text())
    assert provenance['raw_sha256'] == sha256(raw).hexdigest()
    assert provenance['compressed_sha256'] == sha256(frame).hexdigest()
    text = Path('lean/CoveringDesigns/C4k_K_2/Barker.lean').read_text()
    text = text.split('def blocks :', 1)[1].split('/-- Distinctness', 1)[0]
    lean = [[int(x) for x in re.findall(r'\d+', b)] for b in re.findall(r'\{([^{}]+)\}', text)]
    assert lean == [[x-1 for x in b] for b in blocks], 'Barker Lean ordered transcription'
    return {'points': 44, 'block_size': 11, 'distinct_blocks': 21, 'pairs_covered': 946,
            'json_archive_lean_correspondence': True, 'credit': data['credit'],
            'licence': data['licence'], 'raw_sha256': sha256(raw).hexdigest()}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
